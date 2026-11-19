#!/usr/bin/env python3
"""Read-only lexical solver-opportunity survey of Xv6 and MachCSL.

Run from any directory. No Lean/build/solver is started. Patterns may overlap;
counts measure explicit syntax, not runtime cost, applicability, or savings.
"""
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('lean_lint', ROOT / 'tools/lean_lint.py')
lint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lint)
PATTERNS = {
    'omega': r'\bomega\b',
    'bv_omega_whole_context': r'\bbv_omega\b',
    'bv_omega_goal_only': r'\bbv_omega_g\b',
    'bv_decide': r'\bbv_decide\b',
    'grind': r'\bgrind\b',
    'simp_all': r'\bsimp_all\b',
    'k_norm': r'\bk_norm(?:_g|_goal|_all)?\b',
    'bitvec_nat_bridge': r'BitVec\.(?:toNat|ofNat|toInt|ofInt|toNat_add|toNat_sub|toNat_ofNat|toNat_mul|toNat_mod|toNat_udiv)\b',
    'bit_extract_extend': r'BitVec\.(?:signExtend|zeroExtend|extractLsb\x27?|setWidth)\b',
    'nat_div_mod': r'Nat\.(?:mod|div|mod_eq_of_lt|mod_lt|div_lt_iff_lt_mul|div_add_div_same|mul_div_cancel_left|mul_mod)\b|\s(?:%|/)\s',
    'nat_subtraction_syntax': r'\s-\s',
    'list_observation': r'List\.(?:getElem\x27?|getElem\?|getElem!|getD|getElem\?_append|getElem\?_take|getElem\?_drop|getElem\?_set|ext_getElem\?|ext_getElem|length_take|length_drop|length_append|length_set)(?![\w\x27?])',
    'list_rearrangement': r'List\.(?:take|drop|append|set|map|mapIdx|replicate|take_append|drop_append|take_left\x27?|drop_left\x27?|append_assoc|take_drop|drop_drop)\b',
    'finite_map_laws': r'(?:LawfulPartialMap|PartialMap)\.[\w?\x27]+|\b(?:get\?_insert|get\?_delete|insert_insert_comm|insert_get\?)\b',
    'ghost_map_operations': r'\bghost_map_[\w\x27]+\b',
    'resource_accessors': r'\b(?:byteBuf|umPages|ptreeOwn|ptOwnRep|wordPointsTo|pageOwn)[\w\x27]*_(?:acc|split|join|lookup|intro|elim)[\w\x27]*\b|BigSep[LM]\.[\w\x27]*(?:acc|lookup)[\w\x27]*',
    'fraction_resources': r'\bDFrac\.[\w]+\b',
    'set_disjoint_subset': r'\b(?:Disjoint|disjoint|subseteq|subset|Subset|mem_union|mem_inter|mem_diff|mem_insert)\b|##',
    'cpu_pin': r'\bhpin[\w\x27]*\b|wpNext_(?:shift|at)\b',
    'register_updates': r'RegMap\.(?:set_apply|set|reduceApply|set_other|set_apply_of_eq)\b',
    'instruction_dispatch': r'\b(?:k_step|k_step_gen|uk_step|uwk_run|swp_run|kernel_walk)\b',
    'branch_case_split': r'\b(?:by_cases|split|split_ifs)\b',
    'named_decision_equation': r'\b(?:kernel_rfl|kernel_eq_refl|fsimg_decide|binary_rfl)\b',
}
RXS = {k: re.compile(v) for k, v in PATTERNS.items()}
COMMAND = re.compile(r'^(?:@\[[^\n]*\][ \t]*)?(?:(?:private|protected|noncomputable)[ \t]+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class|end|namespace|section|variable|set_option|attribute|open|import)\b[ \t]*([^ \t\n:(]*)', re.M)
SUITE = re.compile(r'\bsimp\s+only\s*\[([^\]]+)\]')
ASSESSMENT = {
    'ranked_angles': [
        {
            'rank': 1,
            'angle': 'External unsat-core selection plus small kernel-replayed arithmetic proofs',
            'evidence': ['mixed_machine_integer_arithmetic cohort', 'arithmetic_with_many_subtraction_terms cohort', 'whole_context_bv_in_large_proofs cohort', 'claude-notes/optimization.md:850', 'claude-notes/optimization.md:863'],
            'new_relative_to_existing': 'bv_omega_g normalizes only the goal; it cannot select necessary hypotheses. KNormCache caches simplification but does not remove irrelevant arithmetic assumptions. A Z3 core can identify the necessary premises, after which Lean omega/bv reasoning proves the original goal from those premises.',
            'first_clients': ['Xv6/ProofScheduler.lean:scheduler_setup', 'Xv6/ProofStrncpy.lean:sy_sub1,sy_pad_w,sy_subw_pad', 'Xv6/ProofUvmcopy.lean:uvmcopy_epi', 'Xv6/UkGrepLoopFrame.lean:grepLoop_epi'],
            'robustness_test': 'Rename/reorder hypotheses, add 0/8/16 irrelevant subtraction-chain facts, and remove the sole necessary bound. Report solved/failed obligations and diagnostic quality; final proof is always kernel-checked.',
            'success_metric': 'Stable results and bounded replay work under context growth; smaller proof dependencies; end-to-end elaboration includes solver IPC and replay.',
        },
        {
            'rank': 2,
            'angle': 'Typed BV/Nat word-level planning instead of flattening all machine facts into modular integer arithmetic',
            'evidence': ['bitvec_nat_bridge frequency', 'bit_extract_extend frequency', 'Xv6/ProofStrncpy.lean:sy_pad_w', 'Xv6/CopyLemmas.lean:co_n_val3', 'Xv6/ProofShParseexec.lean:wp_shParseexec'],
            'new_relative_to_existing': 'Existing bv_decide and bv_omega are already used. The missing planning layer chooses which terms stay bitvectors, which get bounded Nat views, and which shared carries/wrap conditions need proofs. It should emit a small sequence of existing bridge lemmas plus sliced arithmetic, rather than reify an entire symbolic machine state.',
            'first_clients': ['Xv6/ProofStrncpy.lean:sy_pad_w,sy_subw_pad', 'Xv6/CopyLemmas.lean:co_n_val3,co_offB', 'Xv6/ProofShParsecmd.lean:wp_shParsecmd'],
            'robustness_test': 'Equivalent arithmetic reassociation, 32/64-bit width changes, positive/zero/saturating-subtraction boundaries, and rejection of missing no-wrap/sign bounds.',
            'success_metric': 'One clear typed certificate per arithmetic intent; preserve exact theorem statements and audit added axioms; measure solver+replay rather than solver time alone.',
        },
        {
            'rank': 3,
            'angle': 'SMT-style read-over-write normal forms over finite maps and indexed sequence views',
            'evidence': ['finite_map_case_reasoning cohort', 'sequence_observation_and_arithmetic cohort', 'Xv6/FsAbsDelta.lean', 'Xv6/HfpReg.lean:pool_give', 'Xv6/FsCrashSector.lean:fsBlocks_splice'],
            'new_relative_to_existing': 'Archived Sequence/SequenceShapes already offer index search and shared splice templates, and FsAbsDelta already supplies operation-specific delta laws. New work should generate an observation-level store/select certificate and necessary key/index cases across maps AND views, while keeping implementations opaque. It must not merely rerun unrestricted grind or restore a template library.',
            'first_clients': ['Xv6/FsDurImgView.lean:fsDurImgDelete_insertNe', 'Xv6/HfpReg.lean:pool_give', 'Xv6/FsCrashSector.lean:fsBlocks_splice', 'Xv6/EchoOutPure.lean:readWindow_prefix'],
            'robustness_test': 'Reorder independent updates, insert overwritten writes, rename keys, vary clipping bounds, and reject missing key disequalities or out-of-range list observations.',
            'success_metric': 'Proofs state update semantics and footprint, with generated pointwise cases; kernel replay must reuse established lookup/length laws. Ghost authority and crash protocol remain explicit.',
        },
        {
            'rank': 4,
            'angle': 'Resource-routing planner with explicit fraction, extent, and restoration constraints',
            'evidence': ['resource_accessors frequency', 'spatial_accessor_composition cohort', 'Xv6/ProofCopyin.lean:ci_move', 'Xv6/ProofCopyout.lean:copyout_move', 'Xv6/UserHeap.lean:uinstrIs_ukInstr'],
            'new_relative_to_existing': 'BigSep accessors, FrameFilter, LayoutResources, and archived typed Access certificates already perform individual splitting/composition. New capability would infer a valid sequence of existing spatial rules from desired read/write windows, preserving linear restoration continuations and fraction constraints, and explain impossible overlap/width requests.',
            'first_clients': ['Xv6/ProofCopyin.lean:ci_move', 'Xv6/UMemLemmas.lean:byteBuf_split_td', 'Xv6/ByteWord4.lean:byteBuf_word4_at'],
            'robustness_test': 'Alter padding, source fraction, slice nesting, ownership order and alias constraints; solver must reject full-write requests backed only by fractional ownership.',
            'success_metric': 'User supplies access intent and real domain invariant; planner derives a replayable route. Do not ask external arithmetic to invent ghost resources or justify invariant opening.',
        },
        {
            'rank': 5,
            'angle': 'Shared symbolic DAG certificates and cutpoint obligation diagnostics',
            'evidence': ['repeated_exact_simp_suites', 'claude-notes/optimization.md:1090', 'MachCSL/KNormCache.lean', 'Experiments/WholeFunction/CopyinBlocks.lean'],
            'new_relative_to_existing': 'KNormCache already caches within declarations; uwk_run +merge already merges equal-state branches; the current whole-function backend already decodes and symbolically computes blocks. The next distinction is sharing parameterized proofs across blocks/declarations and surfacing only unsolved invariant/resource obligations, rather than rebuilding a second interpreter.',
            'first_clients': ['Xv6/ProofScheduler.lean:scheduler_setup', 'Xv6/ProofMappages.lean:mappages_loop', 'Experiments/WholeFunction/CopyinBlockFacts.lean'],
            'robustness_test': 'Equivalent register allocation and branch refactoring regenerate a certificate without changing domain invariants; wrong targets and insufficient call contracts yield focused failures.',
            'success_metric': 'Fewer brittle intermediate-state annotations; predictable diagnostics; separately measure certificate regeneration, shared helper check, and cached consumer check.',
        },
    ],
    'existing_engines_not_to_reinvent': [
        {'source': 'MachCSL/URunRW.lean', 'capability': 'Write-capable Sail event interpreter and swp importer; ownership footprint and oracle handling already proved.'},
        {'source': 'MachCSL/KNormCache.lean', 'capability': 'Per-declaration simp cache keyed by lemma context with stale-hypothesis detection.'},
        {'source': 'MachCSL/WpSmodeFrame.lean:39', 'capability': 'Literal-index update/read reduction; see RegMap.reduceApply and optimization.md lane K.'},
        {'source': 'MachCSL/FrameFilter.lean', 'capability': 'Head/unification filtering for spatial frame search.'},
        {'source': 'Xv6/KernelTac.lean', 'capability': 'Goal-only bv_omega_g and closed kernel_eq_refl.'},
        {'source': 'MachCSL/UWalkRun.lean:196', 'capability': 'Existing symbolic walker branch merging; inspect uwk_run +merge before proposing path merging.'},
        {'source': 'Xv6/FsAbsDelta.lean', 'capability': 'Pure filesystem map-transition algebra; resource/protocol boundaries remain substantive.'},
        {'source': 'Experiments/LayoutResources.lean', 'capability': 'Existing deterministic record ownership routing.'},
    ],
    'archived_evidence': {
        'ref': 'archive/requisiteness-experiments-20261118',
        'source': 'Requisiteness/README.md',
        'findings': [
            'General kernel reduction of SAT certificates approached 3.3 GiB on tiny examples; direct bit proofs were cheaper. Do not indiscriminately bit-blast all VCs.',
            'Restricted per-client sequence grind made five focused module medians sum 28.447 -> 34.173 seconds; reduced source was not faster checking.',
            'Shared sequence certificates improved incremental checks versus per-client search (35.671 -> 27.041 seconds), but the 8.359-second helper erased first-pass savings.',
            'Unfolding overwrite exhausted grind case-split limits; lookup/length observations made the same theorem succeed. Preserve opaque data-structure representations.',
            'Typed resource access certificates passed six integrations but aggregate median improvement was only 2.8% before helper cost; algebra alone is not an automatic planner.',
            'CPU pin equality closure survived renaming/reordering/reversal and inserted hops; already explored and not a new primary target.',
            'Early benchmark rounds did not explicitly pass -j1; only later sequence/access rounds enforced one Lean worker. Historical measurements are not new results.',
        ],
    },
    'current_negative_evidence': [
        {'source': 'Experiments/README.md:37', 'finding': 'Restricted grind field lookup increased a paired module median from 2.542 to 4.545 seconds; deterministic routing retained.'},
        {'source': 'Experiments/WholeFunction/RequisiteObstruction.lean', 'finding': 'Exact ownState cannot coexist with production resourceInv under stateInterp. Pure external certificates need the footprint/resource boundary, not extra exact-state ownership.'},
        {'source': 'Experiments/WholeFunction/CopyinBlocks.lean', 'finding': 'Current branch equality debugging found global simp recursion; restricted simp only plus kernel_rfl succeeded. New solvers should publish narrow observation/replay interfaces.'},
    ],
    'evaluation_priority': ['unchanged semantic statements', 'transparent proof intent', 'robustness to harmless context/layout changes', 'focused counterexample/failure diagnostics', 'total solver+kernel replay time and peak RSS', 'axiom-set audit'],
    'not_claimed': 'No new speed, robustness, or solver-coverage result follows from these static counts. No LOC-saving target is used. This survey changes no production proof.',
}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

def main():
    totals = {k: Counter() for k in PATTERNS}
    examples = {k: [] for k in PATTERNS}
    files = {k: Counter() for k in PATTERNS}
    thms = []
    suites = defaultdict(list)
    manifest = []
    tree_counts = Counter()
    options = []
    for path in sorted([*ROOT.glob('Xv6/**/*.lean'), *ROOT.glob('MachCSL/**/*.lean')]):
        rel = str(path.relative_to(ROOT))
        src = path.read_text()
        digest = hashlib.sha256(src.encode()).hexdigest()
        manifest.append((rel, digest))
        tree = rel.split('/')[0]
        tree_counts[tree] += 1
        code = lint.blank_comments_and_strings(src)
        for key, rx in RXS.items():
            matches = list(rx.finditer(code))
            if matches:
                files[key][rel] = len(matches)
                totals[key][tree] += len(matches)
                for m in matches[:2]:
                    if len(examples[key]) < 8:
                        examples[key].append({'path': rel, 'line': code.count('\n', 0, m.start()) + 1, 'token': m[0]})
        cmds = list(COMMAND.finditer(code))
        for j, cmd in enumerate(cmds):
            if cmd[1] not in ('theorem', 'lemma'):
                continue
            stop = cmds[j + 1].start() if j + 1 < len(cmds) else len(code)
            text = code[cmd.start():stop]
            rhs = re.search(r':=|\bwhere\b', text)
            body = text[rhs.end():] if rhs else ''
            counts = {key: len(rx.findall(body)) for key, rx in RXS.items()}
            counts = {k: v for k, v in counts.items() if v}
            line = code.count('\n', 0, cmd.start()) + 1
            row = dict(path=rel, theorem=cmd[2], line=line, body_lines=sum(bool(s.strip()) for s in body.splitlines()), counts=counts)
            thms.append(row)
            for match in SUITE.finditer(body):
                terms = ' '.join(match[1].split())
                if len(terms) < 35 or len(terms) > 400:
                    continue
                suites[terms].append(dict(path=rel, theorem=cmd[2], line=line + text[:rhs.end() + match.start()].count('\n')))
        for m in re.finditer(r'set_option[ \t]+(maxHeartbeats|maxRecDepth)[ \t]+(\d+)', code):
            options.append(dict(path=rel, line=code.count('\n', 0, m.start()) + 1, option=m[1], value=int(m[2])))
    def pred(name, condition, key):
        picked = [t for t in thms if condition(t['counts'])]
        return dict(name=name, theorem_count=len(picked), file_count=len({t['path'] for t in picked}),
                    representatives=sorted(picked, key=lambda t: key(t['counts']), reverse=True)[:12])
    cohorts = [
        pred('mixed_machine_integer_arithmetic', lambda c: c.get('bitvec_nat_bridge', 0)>0 and sum(c.get(k,0) for k in ('omega','bv_omega_whole_context','bv_omega_goal_only'))>0,
             lambda c: c.get('bitvec_nat_bridge',0) + c.get('omega',0)),
        pred('arithmetic_with_many_subtraction_terms', lambda c: c.get('omega',0)>0 and c.get('nat_subtraction_syntax',0)>=8,
             lambda c: c.get('nat_subtraction_syntax',0)),
        pred('sequence_observation_and_arithmetic', lambda c: c.get('list_observation',0)>0 and c.get('omega',0)>0,
             lambda c: c.get('list_observation',0)+c.get('list_rearrangement',0)),
        pred('finite_map_case_reasoning', lambda c: c.get('finite_map_laws',0)>0 and c.get('branch_case_split',0)>0,
             lambda c: c.get('finite_map_laws',0)+c.get('branch_case_split',0)),
        pred('spatial_accessor_composition', lambda c: c.get('resource_accessors',0)>=3,
             lambda c: c.get('resource_accessors',0)),
        pred('whole_context_bv_in_large_proofs', lambda c: c.get('bv_omega_whole_context',0)>0 and c.get('instruction_dispatch',0)>=4,
             lambda c: c.get('bv_omega_whole_context',0)*c.get('instruction_dispatch',0)),
    ]
    frequencies = {key: dict(occurrences=sum(totals[key].values()), by_tree=dict(totals[key]), file_count=len(files[key]),
                             top_files=[dict(path=p, occurrences=n) for p,n in files[key].most_common(8)], examples=examples[key]) for key in PATTERNS}
    report = dict(method='Lexical scan after repository comment/string blanker. Pattern counts overlap and include definitions; theorem cohorts inspect lexical theorem RHS. Subtraction syntax is not type-inferred: Nat-subtraction cohort includes BV/Int subtraction and is a candidate list, not established omega complexity. No benchmarks, builds, or solvers run.',
                  production_changes=0, head=git('rev-parse','HEAD').strip(), source_manifest_sha256=hashlib.sha256(json.dumps(manifest).encode()).hexdigest(),
                  modules=dict(tree_counts), theorem_declarations=len(thms), patterns=PATTERNS, frequencies=frequencies, cohorts=cohorts,
                  repeated_exact_simp_suites=[dict(lemmas=s, occurrences=len(xs), files=len({x['path'] for x in xs}), examples=xs[:4]) for s,xs in sorted(suites.items(),key=lambda kv:len(kv[1]),reverse=True)[:15]],
                  enlarged_limits=dict(count=len(options), top=sorted(options,key=lambda x:x['value'],reverse=True)[:15]), assessment=ASSESSMENT)
    report['sources_unchanged_during_scan'] = all(sha == hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path,sha in manifest)
    output = Path(__file__).with_name('report.json')
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(modules=report['modules'],theorems=len(thms),frequencies={k:(v['occurrences'],v['file_count']) for k,v in frequencies.items()},cohorts=[{k:v for k,v in c.items() if k!='representatives'} for c in cohorts]),indent=2))

if __name__ == '__main__':
    main()
