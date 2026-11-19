#!/usr/bin/env python3
"""Reproducible source-size audit; no Lean process or generated-code claims.

Run from any directory. Counts are lexical, not predicted removable LOC.
Theorem bodies use top-level command boundaries and the first := or where.
Comments and strings are blanked by the repository's existing lexer.
"""
import argparse
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
FAMILY = ['Copyin', 'Copyout', 'Copyinstr', 'EitherCopyin', 'EitherCopyout',
          'Walk', 'Walkaddr', 'Vmfault', 'Mappages', 'Uvmcreate', 'Uvmalloc',
          'Uvmdealloc', 'Uvmunmap', 'Uvmfree', 'Uvmcopy', 'Uvmclear',
          'Freewalk', 'Ismapped']
SUPPORT = ['CopyLemmas', 'UPtCopyLemmas', 'UPtDefs', 'UPtLemmas',
           'UPtAllocLemmas', 'UPtFaultLemmas', 'UPtFreeLemmas',
           'UPtUnmapLemmas', 'UPtWalkaddrLemmas', 'PtOwn', 'PtOwnLemmas',
           'PtRunLemmas', 'UMem', 'UMemLemmas', 'UMemWindow', 'UMemLazy',
           'UMemImg', 'UvmCallSites', 'UvmallocDefs', 'VmfaultDefs',
           'VmfaultQuiet', 'WalkaddrDefs']
COMMAND = re.compile(r'^(?:@\[[^\n]*\][ \t]*)?(?:(?:private|protected|noncomputable)[ \t]+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class|end|namespace|section|variable|set_option|attribute|open|import)\b[ \t]*([^ \t\n:(]*)', re.M)
GENERIC_NAME = re.compile(r'(^wp_prologue|^wp_epilogue|_ret_|_br_|Frame|frame.*_(split|join)|_epi$|_call$|Kept|Keep|_setReg|^calleeSaved|^kctx_)')
DOMAIN_NAME = re.compile(r'(fault_leaf|fault_maxva|fault_ro|rpre|wpre|rmapped|wmapped|noNul|page_byte|_inv|Inv|umPages|procPtAt|ptRep|view|mapped|leaf|mapRun)', re.I)
TACTICS = {
    'instruction_step_lines': re.compile(r'\bk_step(?:_gen)?\b'),
    'iris_structural_lines': re.compile(r'\b(?:iintro|iframe|iexact|iapply|isplitl|isplitr|icases|ihave|iexists|idestruct|inext)\b'),
    'interrupt_transport_lines': re.compile(r'\b(?:wpNext_[\w]+|wpNext|withSpie)\b'),
    'normalization_lines': re.compile(r'\b(?:k_norm(?:_g)?|simp|simp_all|simpa|omega|bv_decide|decide|rfl|rw)\b'),
}
AUDIT = {
    'first_end_to_end_target': {
        'function': 'copyin',
        'replacement_type': '(WA : WALKADDR) -> (VF : VMFAULT) -> (MM : MEMMOVE) -> COPYIN',
        'old_module': 'Xv6/ProofCopyin.lean',
        'link_module': 'Xv6/LinkCopyin.lean',
        'deletion_gate': 'Derive the unchanged COPYIN interface without importing ProofCopyin or copying ci_page/ci_move/ci_nsel/ci_iter. Replace the link input and check clients. Source search found no external references to those local helper names.',
        'entry': [
            '50 <= k.avail; k.noff + 1 < 2^31; kmem absent from held locks',
            'a0 = pageAddr P.root; a1.toNat <= 2^38; a4 = old.length modulo 2^64; old.length < 2^63',
            'kctx and pcIs(copyin), kmem lock invariant, uncounted allocator availability',
            'procPtAt P M (well-formed table, full tree and every mapped user page), full destination byteBuf, actLend k.proc ke',
        ],
        'return': [
            'PC = jumpPc(entry ra); calleeSaved(entry regs, returned regs), restoring stack ownership',
            'kctx ((k.withSpie spie spp).withRegs R); when entry sie=false, original spie and spp',
            'wpNext permits migration to any hart if sie=true and proc != 0; otherwise current hart',
            'actLend k.proc k2 with ke <= k2; table P.extSz psz P2 and procPtAt P2(viewFaulted P P2 M)',
            'a0=0: destination equals entire umemRead of final faulted view; all bytes mapped and readable in P2',
            'a0=-1: destination is a copied prefix d<=len plus old.drop d; some e<len is unreadable at wrapped entry src+e in ENTRY P',
            'Continuation must resume actual wpLoop; return is not a language value (MachCSL Val is empty)',
        ],
        'control_flow': [
            'len=0 branch returns before allocating the 12-slot local stack frame',
            'Loop at function+0x5a; failure/success epilogue at function+0x7c; zero-length return at +0x98/+0x9a',
            'WALKADDR selects existing leaf; VMFAULT can fail or allocate a zeroed user R/W page; MEMMOVE copies a page-bounded chunk',
            'Loop retains mapped/readable copied prefix so later lazy faults cannot erase it',
        ],
    },
    'generic_vs_substantive': {
        'generic_candidates': [
            'Binary decoding and instruction resources, instruction dispatch, register substitution, bit-vector normalization',
            'ABI spill/restore, return-address constants, callee-saved transitivity, stack-budget arithmetic',
            'wpNext migration/interrupt continuation transport and routine spatial frame routing',
        ],
        'substantive_invariants_to_retain': [
            'Physical byte ownership and disjointness; table/leaf correspondence; fractional source buffer permission for copyout',
            'Fresh-page zeroing and preservation of already copied/written mapped prefixes',
            'Copy success permissions and ENTRY-table fault witnesses, distinct for reads and writes',
            'copyinstr first-NUL behavior, including NUL in returned prefix; max exhaustion and failed-fault partial copies',
            'Page-allocation freshness, rollback of partial allocations, persistent null-allocation receipt, monotone lend counts',
            'uvmalloc supports unbounded requested size under lazyFree, relying on finite-memory coverage, not a simple cursor bound',
            'uvmunmap has raw, process-space, and bare-table interfaces; these ownership representations are not interchangeable',
        ],
        'interpretation': 'Declaration categories are deliberately conservative. Most large functions mix generic execution with real invariants. Tactic-marker counts do not prove deletability; a generic compiler must separate those concerns once.',
    },
    'architecture_acceptance': [
        'A kernel-checked decoder table is necessary but does not establish execution, memory effects, calls, or interruption handling.',
        'An abstract CopyEffects trace theorem is useful only if actual binary execution constructs that trace without handwritten per-loop-body adapters.',
        'A Region-to-WP theorem must not leave the original whole-program safety proof as a per-function black-box premise.',
        'An exact-state boundary alone cannot produce procPtAt/byteBuf resources. RequisiteObstruction additionally proves ownState conflicts with the production resource invariant under stateInterp, because both own the exclusive ExactState fragment. Prove a different footprint simulation or invariant-aware boundary, with framing/allocator/interference, once.',
        'Generic code must consume actual ABI/callee contracts and loop invariants, then discharge non-cutpoint execution and cutpoint transitions mechanically.',
        'Measure deleted old proof/support minus all new engine, generated certificate source, invariant and adapter lines. Retained specs/shared lemmas do not count as deletions.',
        '5k net LOC is impossible from the three copy modules alone; target the broader page family. 10k requires replacing most of it with very low per-function overhead.',
    ],
    'shared_support_warning': 'CopyLemmas, UPtCopyLemmas, UvmCallSites, UvmallocDefs, WalkaddrDefs and UMemLemmas have consumers outside this family. Reverse imports are included in every file row. Removal requires declaration-level reference audit, not whole-file credit.',
    'validation_plan': [
        'Positive: generated full copyin certificate has exactly existing COPYIN type under same three callee contracts.',
        'Negative: mutate decoded instruction byte/branch displacement and require certificate rejection.',
        'Negative: omit vmfault failure edge, mapped-prefix invariant, continuation hart condition, or necessary stack resource and require rejection.',
        'Generalization: unchanged compiler accepts copyout writable-page check and copyinstr nested NUL loop with only abstract invariants/callee descriptions.',
        'Measure elaboration wall time and peak RSS serially with focused memory-capped checker; no full xv6 rebuild required for first gate.',
    ],
}

def nonempty(s):
    return sum(bool(line.strip()) for line in s.splitlines())

def classify(name, body):
    if GENERIC_NAME.search(name):
        return 'generic_abi_call_and_continuation_bookkeeping'
    if DOMAIN_NAME.search(name) and not re.search(r'\b(?:k_step|k_step_gen)\b', body):
        return 'domain_invariant_or_resource_lemma'
    if re.search(r'\b(?:iintro|iapply|k_step|k_step_gen)\b', body):
        return 'mixed_execution_resource_and_domain_obligations'
    return 'pure_lemma_requires_review_not_assumed_removable'

def scan(path):
    src = path.read_text()
    code = lint.blank_comments_and_strings(src)
    commands = list(COMMAND.finditer(code))
    declarations = []
    for i, cmd in enumerate(commands):
        if cmd[1] not in ('theorem', 'lemma'):
            continue
        stop = commands[i + 1].start() if i + 1 < len(commands) else len(code)
        text = code[cmd.start():stop]
        rhs = re.search(r':=|\bwhere\b', text)
        body = text[rhs.end():] if rhs else ''
        declarations.append(dict(name=cmd[2], line=code.count('\n', 0, cmd.start()) + 1,
                                 proof_body_nonempty_lines=nonempty(body),
                                 category=classify(cmd[2], body)))
    return dict(path=str(path.relative_to(ROOT)), physical_lines=len(src.splitlines()),
                nonempty_code_lines=nonempty(code),
                theorem_body_nonempty_lines=sum(d['proof_body_nonempty_lines'] for d in declarations),
                marker_lines={key: sum(bool(rx.search(line)) for line in code.splitlines()) for key, rx in TACTICS.items()},
                declarations=declarations)

def backend_gap(rows):
    """Disjoint line attribution, restricted to lexical theorem RHS spans.

    Precedence is intentional: full callee-adapter bodies, instruction bundles,
    register case bundles, then explicit markers. Every counted source line has
    one category. This measures recognizable syntax, NOT automatic removability.
    """
    patterns = [
        ('memory_accessor_or_reconstruction', re.compile(r'(?:procPtAt|ptreeOwn|ptOwnRep|umPages|byteBuf|pageOwn|ptree_at|ptOwn_)[\w.\']*')),
        ('callee_application', re.compile(r'\b\w+(?:\.[\w]+)*_call\b|\b[A-Z][A-Z0-9]*\.wp_')),
        ('cpu_continuation', re.compile(r'wpNext_\w+|\bhpin[\w\']*\b|\bhp[0-9]+\s+h\b|\bhsp\w*\s+hh\b|iintro.*%hp\w*')),
        ('register_and_context_normalization', re.compile(r'RegMap\.set|KCtx\.(?:rget|setReg|withRegs)|\bk_norm(?:_g)?\b|\bcalleeSaved\b|\b(?:\w*Kept\w*|ciKeep|coKeep|csKeep|walkPres|uaRegs)\b')),
        ('generic_iris_syntax_not_proven_removable', re.compile(r'^\s*(?:[·|]\s*)?(?:iintro|iframe|iexact|iapply|isplitl|isplitr|icases|ihave|iexists|ipureintro|inext|itrivial|rotate_right)\b')),
    ]
    categories = ['callee_adapter_body', 'instruction_dispatch_and_resume',
                  'register_preservation_case_body'] + [p[0] for p in patterns] + ['other_domain_or_unclassified']
    import collections
    aggregate = collections.Counter({k: 0 for k in categories})
    subdivisions = {key: collections.Counter() for key in ('instruction_dispatch_and_resume', 'cpu_continuation', 'register_and_context_normalization')}
    per_file = []
    examples = {k: [] for k in categories}
    for row in rows:
        if not row['path'].startswith('Xv6/Proof'):
            continue
        code = lint.blank_comments_and_strings((ROOT / row['path']).read_text())
        commands = list(COMMAND.finditer(code))
        labels = {}
        theorem_of_line = {}
        lines = code.splitlines()
        for j, cmd in enumerate(commands):
            if cmd[1] not in ('theorem', 'lemma'):
                continue
            stop = commands[j + 1].start() if j + 1 < len(commands) else len(code)
            rhs = re.search(r':=|\bwhere\b', code[cmd.start():stop])
            if not rhs:
                continue
            start = cmd.start() + rhs.end()
            line0 = code.count('\n', 0, start)
            bodylines = code[start:stop].splitlines()
            eligible = {}
            for offset, text in enumerate(bodylines):
                if text.strip():
                    eligible[line0 + offset] = text
                    theorem_of_line[line0 + offset] = cmd[2]
            if cmd[2].endswith('_call'):
                labels.update({n: 'callee_adapter_body' for n in eligible})
                continue
            for n, text in eligible.items():
                if re.search(r'\bk_step(?:_gen)?\b|\bk_code\b', text):
                    labels[n] = 'instruction_dispatch_and_resume'
                    indent = len(lines[n]) - len(lines[n].lstrip())
                    for k in range(n + 1, max(eligible) + 1):
                        if k not in eligible:
                            continue
                        nxt = eligible[k]
                        if len(nxt) - len(nxt.lstrip()) <= indent:
                            break
                        labels[k] = 'instruction_dispatch_and_resume'
                if re.match(r'^\s*iintro Hk Hpc\s*$', text):
                    labels[n] = 'instruction_dispatch_and_resume'
                if re.match(r"^\s*case (?:[hge][0-9]+[\w']*|hsp[\w']*)\s*=>", text):
                    indent = len(lines[n]) - len(lines[n].lstrip())
                    block = [n]
                    for k in range(n + 1, max(eligible) + 1):
                        if k not in eligible:
                            continue
                        if len(eligible[k]) - len(eligible[k].lstrip()) <= indent:
                            break
                        block.append(k)
                    if any(re.search(r'RegMap\.set|k_norm|KCtx\.|calleeSaved', eligible[k]) for k in block):
                        for k in block:
                            labels.setdefault(k, 'register_preservation_case_body')
            for n, text in eligible.items():
                if n in labels:
                    continue
                labels[n] = next((key for key, rx in patterns if rx.search(text)), 'other_domain_or_unclassified')
        counts = collections.Counter(labels.values())
        assert sum(counts.values()) == row['theorem_body_nonempty_lines'], row['path']
        aggregate.update(counts)
        per_file.append(dict(path=row['path'], theorem_body_nonempty_lines=sum(counts.values()), counts=dict(counts)))
        for n, category in sorted(labels.items()):
            if category in subdivisions:
                text = lines[n]
                if category == 'instruction_dispatch_and_resume':
                    part = 'instruction_tactic_head' if re.search(r'\bk_step(?:_gen)?\b|\bk_code\b', text) else ('bare_Hk_Hpc_intro' if re.match(r'^\s*iintro Hk Hpc\s*$', text) else 'indented_instruction_arguments')
                elif category == 'cpu_continuation':
                    part = 'wpNext_at_or_shift' if re.search(r'wpNext_(?:at|shift)\b', text) else ('other_wpNext' if 'wpNext_' in text else ('explicit_hp_composition' if re.search(r'\bhp[0-9]+\s+h\b|\bhsp\w*\s+hh\b', text) else 'pin_declaration_or_resume'))
                else:
                    part = 'explicit_RegMap_set' if 'RegMap.set' in text else ('k_norm' if re.search(r'\bk_norm(?:_g)?\b', text) else 'other_register_context_fact')
                subdivisions[category][part] += 1
            if len(examples[category]) < 4:
                examples[category].append(dict(path=row['path'], line=n + 1, theorem=theorem_of_line[n], source=lines[n].strip()))
    narrow = sum(aggregate[x] for x in ['instruction_dispatch_and_resume', 'register_preservation_case_body', 'cpu_continuation', 'register_and_context_normalization'])
    nonbody = sum(r['nonempty_code_lines'] - r['theorem_body_nonempty_lines'] for r in rows if r['path'].startswith('Xv6/Proof'))
    return dict(method='Disjoint source-line heuristic over theorem RHS only. Category precedence: complete *_call theorem bodies; instruction dispatch with indented arguments and bare iintro Hk Hpc; numeric-register case blocks containing register normalization; ordered memory/callee/CPU/register/Iris markers; remainder. A line belongs to exactly one category. No fraction of a mixed line is separately counted.',
                actual_production_loc_saved=0, categories=dict(aggregate), recognized_kernel_bookkeeping_gross=narrow,
                within_category_disjoint_breakdowns={k: dict(v) for k, v in subdivisions.items()},
                net_5000_budget_before_any_overhead=narrow - 5000,
                all_nonbody_source_lines=nonbody,
                optimistic_overhead_budget_if_every_nonbody_line_disappeared=narrow + nonbody - 5000,
                scale_assessment='The observed kernel-bookkeeping bodies alone do not reach 5k gross. It is not a mathematical impossibility: deleting duplicated local signatures/definitions can add lines. Even crediting EVERY nonbody line would leave only the reported optimistic overhead budget for engine, certificates and invariants; that extreme includes imports and substantive definitions that actually remain. A credible 5k net plan therefore needs measured signature compression and/or generic resource/callee adaptation, not just register substitution and CPU pin transport.',
                warning='Recognized lines are candidate gross deletions, not established savings. Signature/definition compression could add savings, while engine/certificates/invariants/adapters subtract them. Generic Iris syntax includes domain/resource work and must not be silently credited to a register/CPU backend.',
                examples=examples, files=per_file)

def main():
    paths = [ROOT / 'Xv6' / f'{prefix}{name}.lean' for name in FAMILY for prefix in ('Proof', 'Spec', 'Link')]
    paths += [ROOT / 'Xv6' / f'{name}.lean' for name in SUPPORT]
    rows = [scan(path) for path in paths if path.exists()]
    reverse = {}
    for tree in ('Xv6', 'MachCSL'):
        for path in (ROOT / tree).rglob('*.lean'):
            with path.open() as source:
                header = source.read(32768)
            for module in lint.imports_of(header):
                reverse.setdefault(module, []).append(str(path.relative_to(ROOT)))
    for row in rows:
        module = row['path'][:-5].replace('/', '.')
        row['direct_importers'] = sorted(reverse.get(module, []))
    sums = {}
    for name, pred in {
        'three_copy_proofs': lambda p: p in [f'Xv6/Proof{x}.lean' for x in ('Copyin', 'Copyout', 'Copyinstr')],
        'family_proofs': lambda p: p.startswith('Xv6/Proof'),
        'family_specs': lambda p: p.startswith('Xv6/Spec'),
        'family_links': lambda p: p.startswith('Xv6/Link'),
        'support_not_assumed_removable': lambda p: not any(p.startswith('Xv6/' + x) for x in ('Proof', 'Spec', 'Link')),
    }.items():
        subset = [r for r in rows if pred(r['path'])]
        sums[name] = dict(files=len(subset), **{k: sum(r[k] for r in subset) for k in ('physical_lines', 'nonempty_code_lines', 'theorem_body_nonempty_lines')})
    report = dict(method='Lexical theorem RHS nonempty lines, after blanking comments and strings. Categories are review heuristics; mixed bodies are NOT counted as generic or removable. Markers overlap. Specs and shared support are NOT deletion credits.',
                  family=FAMILY, totals=sums, audit=AUDIT, files=rows)
    out = Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(report, indent=2) + '\n')
    gap = backend_gap(rows)
    Path(__file__).with_name('backend-gap-audit.json').write_text(json.dumps(gap, indent=2) + '\n')
    print(json.dumps(sums, indent=2))
    print(json.dumps({k: v for k, v in gap.items() if k not in ('examples', 'files')}, indent=2))

CLIENT_PATTERNS = {
    'instruction_step_occurrences': r'\b(?:k_step|k_step_gen)\b',
    'spatial_tactic_occurrences': r'\b(?:iintro|iframe|iexact|iapply|isplitl|isplitr|icases|ihave|iexists|idestruct|inext)\b',
    'interrupt_transport_occurrences': r'\bwpNext_(?:shift|at|mono|intro_pin)\b',
    'byte_ownership_accessor_occurrences': r'\bbyteBuf_(?:acc|upd)\b',
}


def client_authoring_report(reference):
    revision = subprocess.check_output(
        ['git', 'rev-parse', '--verify', reference + '^{commit}'], cwd=ROOT, text=True).strip()

    def measure(source):
        code = lint.blank_comments_and_strings(source)
        return {'physical_lines': len(source.splitlines()),
                **{key: len(re.findall(pattern, code)) for key, pattern in CLIENT_PATTERNS.items()}}

    functions = {}
    for name in ['Copyin', 'Copyout', 'Strlen', 'Strncpy']:
        original_path = 'Xv6/Proof' + name + '.lean'
        original = subprocess.check_output(['git', 'show', revision + ':' + original_path], cwd=ROOT)
        # Include the complete function prefix cohort, not merely its thin export.
        clients = sorted(path for path in Path(__file__).parent.glob(name + '*.lean')
                         if not path.stem.endswith(('Audit', 'Axioms', 'Checks')))
        contents = [(path, path.read_bytes()) for path in clients]
        client_counts = measure('\n'.join(data.decode() for _, data in contents))
        client_counts['physical_lines'] = sum(len(data.splitlines()) for _, data in contents)
        functions[name] = {
            'original': {'source': original_path, 'sha256': hashlib.sha256(original).hexdigest(),
                         'counts': measure(original.decode())},
            'client': {'counts': client_counts,
                       'files': {str(path.relative_to(ROOT)): hashlib.sha256(data).hexdigest()
                                 for path, data in contents}},
        }
    return {
        'method': 'Lexical occurrence counts after blanking comments and strings; physical LOC retains both.',
        'scope': 'All function-prefix client files except audit/check modules. Shared engines excluded. '
                 'These cohorts are not dependency closures, proof-effort estimates, or total-code savings.',
        'validation': 'Source inventory only; this report does not assert that current sources compile.',
        'baseline_revision': revision, 'patterns': CLIENT_PATTERNS, 'functions': functions,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clients', action='store_true', help='compare client authoring patterns with original proofs')
    parser.add_argument('--baseline-ref', default='818a8b6a6d38d128130fa0aa7e0c0505d6850feb')
    parser.add_argument('--output', type=Path, help='new report path for --clients; existing reports are preserved')
    args = parser.parse_args()
    if args.clients:
        if args.output is None:
            parser.error('--clients requires a new --output path')
        report = client_authoring_report(args.baseline_ref)
        with args.output.open('x') as output:
            output.write(json.dumps(report, indent=2) + '\n')
        print(json.dumps({name: {variant: data[variant]['counts'] for variant in ['original', 'client']}
                          for name, data in report['functions'].items()}, indent=2))
    elif args.output:
        parser.error('--output requires --clients')
    else:
        main()
