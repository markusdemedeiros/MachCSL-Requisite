"""Hash the full available source and compiled-import closure without Lean."""
import hashlib,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
TOOLCHAIN=Path('/home/agent/.elan/toolchains')/((ROOT/'lean-toolchain').read_text().strip().replace('/', '--').replace(':','---'))
SOURCE_ROOTS=[ROOT,ROOT/'vendor/lean-sail',ROOT/'model/Lean_RV64D',ROOT/'.lake/packages/iris/Iris',ROOT/'.lake/packages/Qq',ROOT/'.lake/packages/batteries',TOOLCHAIN/'src/lean']
ARTIFACT_ROOTS=[p/'.lake/build/lib/lean' for p in SOURCE_ROOTS[:-1]]+[TOOLCHAIN/'lib/lean']

def sha_file(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()

def label(path):
    try:return str(path.relative_to(ROOT))
    except ValueError:return str(path)

def import_header(path):
    text=path.read_text();pattern=r'/-(?:(?!/-|-/)[\s\S])*-/'
    while re.search(pattern,text):text=re.sub(pattern,'',text)
    text=re.sub(r'--[^\n]*','',text)
    out=[];prelude=False
    for line in text.splitlines():
        line=line.strip()
        if not line or line=='module':continue
        if line=='prelude':prelude=True;continue
        hit=re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)',line)
        if hit:
            modules=hit[1].split()
            if modules and modules[0]=='all':modules.pop(0)
            out.extend(modules)
        else:break
    return out if prelude else ['Init']+out

def manifest(client):
    sources={};artifacts={};graph={};missing=[];pending=import_header(client);seen=set()
    while pending:
        module=pending.pop()
        if module in seen:continue
        seen.add(module)
        relative=Path(*module.split('.'))
        source=next((base/relative.with_suffix('.lean') for base in SOURCE_ROOTS if (base/relative.with_suffix('.lean')).exists()),None)
        if source is None:missing.append({'module':module,'kind':'source'});continue
        sources[label(source)]=sha_file(source)
        deps=import_header(source);graph[module]=deps;pending.extend(deps)
        artifact=next((base/relative.with_suffix('.olean') for base in ARTIFACT_ROOTS if (base/relative.with_suffix('.olean')).exists()),None)
        if artifact is None:missing.append({'module':module,'kind':'olean'});continue
        for suffix in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']:
            path=artifact.with_suffix(suffix)
            if path.exists():artifacts[label(path)]=sha_file(path)
    # The generated client is also part of the input, but its output is not.
    sources[label(client)]=sha_file(client)
    for file in ['lakefile.toml','lake-manifest.json','lean-toolchain','Experiments/check.sh']:
        path=ROOT/file
        if path.exists():sources[file]=sha_file(path)
    solver=ROOT/'.lake/solver-python/bin/z3'
    if solver.exists():artifacts[label(solver)]=sha_file(solver)
    return {'sources':sources,'compiled_imports_and_solver':artifacts,'module_imports':graph,'missing':missing}

def changes(snapshot):
    out=[]
    for category in ['sources','compiled_imports_and_solver']:
        for name,sha in snapshot[category].items():
            path=Path(name) if Path(name).is_absolute() else ROOT/name
            if not path.exists() or sha_file(path)!=sha:out.append(name)
    return out
