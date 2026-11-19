#!/usr/bin/env python3
"""Paired, capped scratch-client checks of external SMT selection + Lean replay.

Production files stay untouched. Both variants import the cached engine, so
the paired difference isolates tactic/replay behavior. Helper compilation is
not included; all solver IPC and kernel checking in each client IS included.
Sources are read from --source-ref (HEAD by default), never silently from the
working tree. Reproduce a saved run with its recorded immutable source commit.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('survey', Path(__file__).with_name('audit.py'))
survey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(survey)
OUT = ROOT / '.lake/solver-survey'
ENGINE = ROOT / 'Experiments/SolverSurvey/SmtSlice.lean'
CASES = {
    'strncpy': ('Xv6/ProofStrncpy.lean', ['sy_sub1', 'sy_pad_w', 'sy_subw_pad'], 'bv'),
    'scheduler': ('Xv6/ProofScheduler.lean', ['scheduler_setup'], 'bv'),
    'uvmcopy': ('Xv6/ProofUvmcopy.lean', ['uvmcopy_epi'], 'bv'),
    'grep': ('Xv6/UkGrepLoopFrame.lean', ['grepLoop_epi'], 'grep'),
}

def sha(raw):
    return hashlib.sha256(raw.encode()).hexdigest()

def spans(source, wanted):
    code = survey.lint.blank_comments_and_strings(source)
    commands = list(survey.COMMAND.finditer(code))
    found = {}
    for j, cmd in enumerate(commands):
        if cmd[1] not in ('theorem', 'lemma') or cmd[2] not in wanted:
            continue
        stop = commands[j + 1].start() if j + 1 < len(commands) else len(code)
        rhs = re.search(r':=|\bwhere\b', code[cmd.start():stop])
        assert rhs, cmd[2]
        begin = cmd.start() + rhs.end()
        found[cmd[2]] = (cmd.start(), begin, stop)
    assert set(found) == set(wanted), (wanted, found)
    return code, found

def generate(name, engine='slice', selected_variants=None, source_ref='HEAD'):
    path, decls, mode = CASES[name]
    source_commit = subprocess.check_output(['git','rev-parse',source_ref+'^{commit}'],cwd=ROOT,text=True).strip()
    source = subprocess.check_output(['git','show',source_commit+':'+path],cwd=ROOT,text=True)
    code, targets = spans(source, decls)
    variants = {}
    edits = {}
    options = ('baseline', 'uncleared', 'solver_uncleared') if mode == 'grep' else ('baseline', 'solver')
    if selected_variants:
        options = tuple(v for v in options if v in selected_variants)
        if 'baseline' not in options:
            raise ValueError('baseline is required for the paired axiom audit')
    module = 'SmtLearn' if engine == 'learn' else 'SmtSlice'
    prefix = f'import Experiments.SolverSurvey.{module}\n'
    axiom_lines = '\n' + '\n'.join('#print axioms Xv6.' + n for n in decls) + '\n'
    for variant in options:
        replacements = []
        solver_replacements = 0
        for _, begin, end in targets.values():
            if mode == 'grep' and variant != 'baseline':
                for m in re.finditer(r'^[ \t]*clear hs\d+[ \t]*\n', code[begin:end], re.M):
                    replacements.append((begin+m.start(),begin+m.end(),''))
            if 'solver' in variant:
                nat_tactic, bv_tactic = ('smt_learn','bv_smt_learn') if engine == 'learn' else ('smt_omega','bv_smt')
                word, tactic = ('omega',nat_tactic) if mode == 'grep' else ('bv_omega',bv_tactic)
                for m in re.finditer(r'\b'+word+r'\b', code[begin:end]):
                    replacements.append((begin+m.start(),begin+m.end(),tactic))
                    solver_replacements += 1
        if 'solver' in variant and not solver_replacements:
            raise ValueError(f'{source_commit}:{path} has no baseline tactic sites in {decls}; select the historical source commit from the saved report')
        changed = source
        for a,b,value in sorted(replacements,reverse=True):
            changed = changed[:a] + value + changed[b:]
        # Imports must precede options; put tracing at the first non-import command.
        first = next(m for m in survey.COMMAND.finditer(survey.lint.blank_comments_and_strings(changed)) if m[1] != 'import')
        changed = changed[:first.start()] + 'set_option smtSlice.trace true\n' + changed[first.start():]
        newcode, newtargets = spans(changed,decls)
        for decl in decls:
            a,b,_ = targets[decl]
            x,y,_ = newtargets[decl]
            assert code[a:b] == newcode[x:y], f'statement changed: {decl}'
        raw = prefix + changed + axiom_lines
        dst = OUT / f'{engine}-{name}-{variant}.lean'
        dst.write_text(raw)
        variants[variant] = dst
        edits[variant] = len(replacements)
    return dict(source=path, source_ref=source_ref, source_commit=source_commit, source_sha256=sha(source), declarations=decls, statement_check='identical lexical declaration headers',
                variant_sha256={k:sha(v.read_text()) for k,v in variants.items()}, edit_count=edits), variants

def seconds(raw):
    return sum(float(n)*{'min':60,'s':1,'ms':0.001,'us':0.000001}[unit]
               for n,unit in re.findall(r'([\d.]+)\s*(min|ms|us|s)',raw))

def check(source, tag):
    log = OUT / f'{tag}.log'
    with log.open('w') as stream:
        p = subprocess.run(['bash','Experiments/check.sh',str(source.relative_to(ROOT))],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
    text = log.read_text()
    result = dict(exit_code=p.returncode,log=str(log.relative_to(ROOT)),log_sha256=sha(text))
    for label,key in [('Service runtime','wall_s'),('CPU time consumed','cpu_s')]:
        m=re.search(label+r':\s*(.+)',text)
        if m:result[key]=seconds(m[1])
    m=re.search(r'Memory peak:\s*([\d.]+)([KMG])',text)
    if m:result['peak_mib']=float(m[1])*{'K':1/1024,'M':1,'G':1024}[m[2]]
    result['axioms']={m[1].rstrip("'"):sorted(a.strip() for a in m[2].split(',') if a.strip()) for m in re.finditer(r"'?(Xv6\.[\w.']+)'? depends on axioms:\s*\[(.*?)\]",text,re.S)}
    result['selected_hypotheses']=[dict(selected=int(a),available=int(b)) for a,b in re.findall(r'selected (\d+)/(\d+) arithmetic hypotheses',text)]
    result['learned_lemmas']=len(re.findall(r'smt_learn: learned lemma',text))
    result['reused_lemmas']=len(re.findall(r'smt_learn: reused checked arithmetic lemma',text))
    result['generalization_fallbacks']=len(re.findall(r'smt_learn: generalization unavailable',text))
    if p.returncode:result['error_tail']=text[-5000:]
    print(json.dumps(dict(tag=tag,**{k:v for k,v in result.items() if k not in ('axioms','error_tail','selected_hypotheses')})),flush=True)
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',nargs='+',choices=CASES,default=['strncpy','scheduler'])
    parser.add_argument('--rounds',type=int,default=3)
    parser.add_argument('--engine',choices=('slice','learn'),default='slice')
    parser.add_argument('--variants',nargs='+',choices=('baseline','uncleared','solver','solver_uncleared'))
    parser.add_argument('--report',type=Path,help='Optional report destination, relative to repository root')
    parser.add_argument('--source-ref',default='HEAD',help='Git revision supplying the historical production proof bodies (default HEAD)')
    parser.add_argument('--generate-only',action='store_true')
    args=parser.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    engine_files=[ENGINE]
    if args.engine=='learn':engine_files.append(ROOT/'Experiments/SolverSurvey/SmtLearn.lean')
    engine_start={str(p.relative_to(ROOT)):sha(p.read_text()) for p in engine_files}
    report=dict(method=__doc__,engine=args.engine,engine_sha256=engine_start,rounds=args.rounds,results={})
    workspace_start={path:sha((ROOT/path).read_text()) for path,_,_ in (CASES[n] for n in args.cases)}
    for name in args.cases:
        metadata,variants=generate(name,args.engine,args.variants,args.source_ref)
        print(json.dumps(dict(case=name,variants={k:str(v) for k,v in variants.items()},edits=metadata['edit_count'])),flush=True)
        if args.generate_only:continue
        samples={key:[] for key in variants}
        failed=set()
        for n in range(args.rounds):
            order=list(variants) if n%2==0 else list(reversed(variants))
            for key in order:
                if key in failed:continue
                result=check(variants[key],f'{args.engine}-{name}-{key}-{n}')
                samples[key].append(result)
                if result['exit_code']:failed.add(key)
        baseline=samples['baseline'][0]['axioms'] if samples['baseline'] and samples['baseline'][0]['exit_code']==0 else None
        audit={}
        for key,ss in samples.items():
            if not ss or any(s['exit_code'] for s in ss):continue
            axioms=ss[0]['axioms']
            audit[key]=dict(all_theorems_reported=set(axioms)=={'Xv6.'+d for d in metadata['declarations']},
                            axioms_subset_of_baseline=baseline is not None and all(set(ax).issubset(baseline.get(d,[])) for d,ax in axioms.items()))
        medians={key:{metric:statistics.median(s[metric] for s in ss) for metric in ('wall_s','cpu_s','peak_mib') if all(metric in s for s in ss)} for key,ss in samples.items() if ss and not any(s['exit_code'] for s in ss)}
        report['results'][name]=dict(**metadata,samples=samples,medians=medians,axiom_audit=audit)
        report['engine_unchanged']=all(sha((ROOT/p).read_text())==digest for p,digest in engine_start.items())
        report['workspace_sources_unchanged_during_run']=all(sha((ROOT/path).read_text())==digest for path,digest in workspace_start.items())
        destination=(ROOT/args.report) if args.report else (OUT/('benchmark-'+args.engine+'-'+'-'.join(args.cases)+'.json'))
        destination.write_text(json.dumps(report,indent=2)+'\n')
    if not args.generate_only:
        print(json.dumps({k:dict(medians=v['medians'],audit=v['axiom_audit']) for k,v in report['results'].items()},indent=2))

if __name__=='__main__':main()
