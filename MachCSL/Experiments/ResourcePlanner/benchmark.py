#!/usr/bin/env python3
"""Paired cached-import checks of identical actual client statements.

Both planners and the manual baseline use the same shared window replay rules.
No whole-xv6 build; every Lean process uses the shared serialized 4 GiB wrapper.
"""
import argparse,hashlib,json,re,subprocess,time
from snapshots import manifest,changes,import_header,sha_file,label
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
SCRATCH=ROOT/'.lake/resource-planner'

def digest(b):return hashlib.sha256(b).hexdigest()

WRITE_MANUAL='''  unfold wiSrc
  simp only [user, Bool.false_eq_true, ite_false]
  iintro ⟨⟨HF, Hsource, Hpid⟩, Hdest⟩
  icases read_window src A.dqs A.sbs tot n sourceBound $$ Hsource with ⟨Hs, Hsclose⟩
  icases write_window dst old off n destinationBound $$ Hdest with ⟨Hd, Hdclose⟩
  isplitl [Hs Hd]
  · iframe Hs Hd
  · iintro %new %len ⟨Hs, Hd⟩
    ihave Hsource := Hsclose $$ Hs
    ihave Hdest := Hdclose $$ %new %len Hd
    iframe HF Hsource Hpid Hdest
'''
READ_MANUAL='''  iintro H
  icases dsHold_swap γb V kk pidv dev bno bs bsd $$ H with ⟨Hown, Hback⟩
  unfold bufOwn
  icases Hown with ⟨%len, Hb, Hd, Hbuf⟩
  icases read_window (aBufData (bnode kk)) (DFrac.own 1) bs off n (by omega)
    $$ Hbuf with ⟨Hwin, Hclose⟩
  isplitl []
  · ipureintro; exact len
  isplitl [Hwin]
  · iexact Hwin
  · iintro Hwin
    ihave Hbuf := Hclose $$ Hwin
    iapply Hback $$ %bs
    iframe Hb Hd Hbuf
    ipureintro; exact len
'''

def sources():
    source=(HERE/'Actual.lean').read_text()
    source=source.replace('set_option resourcePlanner.trace true','set_option resourcePlanner.trace false')
    write='  unfold wiSrc\n  simp only [user, Bool.false_eq_true, ite_false]\n  resource_write\n'
    read='  unfold bufHold0 bufOwn\n  resource_read_smt\n'
    assert source.count(write)==source.count(read)==1
    return {
        'manual':source.replace(write,WRITE_MANUAL).replace(read,READ_MANUAL),
        'deterministic':source.replace('resource_read_smt','resource_read'),
        'z3':source.replace('resource_write\n','resource_write_smt\n')}

def runtime(log):
    found=re.search(r'Service runtime:\s*([^\n]+)',log)
    if not found:return None
    units={'min':60,'s':1,'ms':.001,'us':.000001}
    return sum(float(n)*units[u] for n,u in re.findall(r'([0-9.]+)(min|ms|us|s)',found[1]))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rounds',type=int,default=3)
    p.add_argument('--generate-only',action='store_true')
    p.add_argument('--output',type=Path,default=HERE/'benchmark.json')
    a=p.parse_args()
    if a.output.exists() and not a.generate_only:raise SystemExit('Refusing to overwrite '+str(a.output))
    work=SCRATCH/('run-'+digest(str(a.output.resolve()).encode())[:12])
    work.mkdir(parents=True,exist_ok=True)
    variants=sources()
    paths={k:work/(k+'.lean') for k in variants}
    for k,s in variants.items():paths[k].write_text(s)
    # Exact declaration headers are preserved by body-only substitutions.
    headers=lambda s:re.findall(r'theorem\s+[\s\S]*?:= by',s)
    assert all(headers(s)==headers(next(iter(variants.values()))) for s in variants.values())
    if a.generate_only:
        print('Generated exact-header-equivalent variants:',','.join(variants));return
    if a.output.exists():raise SystemExit('Refusing to overwrite '+str(a.output))
    hashes={str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in HERE.glob('*.lean')}
    snapshot=manifest(paths['manual'])
    assert all(import_header(path)==import_header(paths['manual']) for path in paths.values())
    for path in list(paths.values())+[HERE/'Actual.lean',HERE/'benchmark.py',HERE/'snapshots.py']:
        snapshot['sources'][label(path)]=sha_file(path)
    if snapshot['missing']:raise SystemExit('Incomplete import closure: '+str(snapshot['missing']))
    samples=[];expected_axioms=None
    for round in range(a.rounds):
        order=list(variants);order=order[round%3:]+order[:round%3]
        for name in order:
            path=paths[name];logpath=work/f'{name}-{round+1}.log'
            before_changes=changes(snapshot)
            if before_changes:raise SystemExit('Input closure changed: '+str(before_changes))
            start=time.monotonic()
            with logpath.open('w') as log:
                result=subprocess.run(['bash','Experiments/check.sh','-o',str(path.with_suffix('.olean')),str(path.relative_to(ROOT))],cwd=ROOT,stdout=log,stderr=log)
            log=logpath.read_text();bad='sorryAx' in log or 'declaration uses \'sorry\'' in log
            sample={'variant':name,'round':round+1,'exit_code':result.returncode or int(bad),
                'service_seconds':runtime(log),'wall_including_lock':round_number(time.monotonic()-start),
                'log':str(logpath.relative_to(ROOT)),'source_sha256':digest(path.read_bytes()),
                'axioms':re.findall(r"'([^']+)' depends on axioms:\s*(\[[\s\S]*?\])",log),
                'peak':(re.search(r'Memory peak:\s*([^\n]+)',log)[1] if re.search(r'Memory peak:\s*([^\n]+)',log) else None)}
            sample['closure_changes_after']=changes(snapshot)
            parsed_axioms={theorem:sorted(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',values)) for theorem,values in sample['axioms']}
            if expected_axioms is None and sample['exit_code']==0:expected_axioms=parsed_axioms
            sample['axiom_sets_match']=len(parsed_axioms)==2 and parsed_axioms==expected_axioms
            sample['accepted']=sample['exit_code']==0 and sample['axiom_sets_match'] and not sample['closure_changes_after']
            if not sample['accepted']:sample['exit_code']=sample['exit_code'] or 1
            samples.append(sample);print(name,round+1,sample['exit_code'],sample['service_seconds'],flush=True)
            if sample['exit_code']:break
        if samples[-1]['exit_code']:break
    changed=[k for k,v in hashes.items() if digest((ROOT/k).read_bytes())!=v]
    import statistics
    medians={k:statistics.median(s['service_seconds'] for s in samples if s['variant']==k and s['exit_code']==0 and s['service_seconds'] is not None)
             for k in variants if any(s['variant']==k and s['exit_code']==0 and s['service_seconds'] is not None for s in samples)}
    out={'scope':'Actual Writei kernel copy boundary and exact Readi hold-window statement; cached imports; manual and automated variants use same replay lemmas.',
         'source_hashes':hashes,'sources_changed':changed,'full_import_closure':snapshot,'expected_axiom_sets':expected_axioms,'samples':samples,'median_service_seconds':medians,
         'statement_headers_equal':True,'memory_gib':4,'workers':1,
         'limitations':['Not a whole-build measurement. Shared rule/planner compilation is excluded.','Manual baseline uses the same window replay rules; it is not the original hand-split Readi proof body.','Current assignment supports one window per source atom; buffer-fragment planning is not implemented.','Z3 solves finite injective matching; the deterministic algorithm solves the same problem.']}
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    raise SystemExit(int(bool(changed) or any(s['exit_code'] for s in samples)))

def round_number(x):return round(x,3)
if __name__=='__main__':main()
