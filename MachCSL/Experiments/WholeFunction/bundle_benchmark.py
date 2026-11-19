#!/usr/bin/env python3
"""Compare identical Lean source work separately and concatenated, with capped checks.

Only experiment modules in the selected source closure are bundled. Authored
sources remain unchanged. Generated sections preserve local scopes; private
locals are alpha-renamed to preserve per-module name isolation. Imports outside
that closure use cached oleans.
This is a packaging experiment, not a clean xv6 build benchmark.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "Experiments.WholeFunction."
IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)


def imports(data):
    return IMPORT.findall(data)


def source(module):
    return ROOT / (module.replace('.', '/') + '.lean')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', default='CopyoutEntry')
    parser.add_argument('--scope', default='Copyout', help='Selected module stem prefix, or all')
    parser.add_argument('--tag', required=True)
    parser.add_argument('--individual', action='store_true')
    parser.add_argument('--import-controls', action='store_true')
    args = parser.parse_args()
    out = ROOT / '.lake/whole-function/bundles' / args.tag
    out.mkdir(parents=True, exist_ok=False)
    selected, seen, externals = [], set(), set()
    contents = {}

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        if not module.startswith(PREFIX) or (args.scope != 'all' and not module.removeprefix(PREFIX).startswith(args.scope)):
            externals.add(module)
            return
        data = source(module).read_text()
        contents[module] = data
        for dep in imports(data):
            visit(dep)
        selected.append(module)

    visit(PREFIX + args.target)
    external_closure = set()

    def external_visit(module):
        if module in selected:
            raise RuntimeError(f'external import silently reimports bundled module: {module}')
        if module in external_closure:
            return
        external_closure.add(module)
        path = source(module)
        if path.exists():
            for dep in imports(path.read_text()):
                external_visit(dep)

    for module in externals:
        external_visit(module)
    manifest = {
        'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'target': args.target, 'scope': args.scope,
        'sources': [{'module': m, 'sha256': hashlib.sha256(contents[m].encode()).hexdigest(),
                     'lines': len(contents[m].splitlines())} for m in selected],
        'external_imports': sorted(externals),
        'external_source_hashes': {m: hashlib.sha256(source(m).read_bytes()).hexdigest()
                                   for m in sorted(external_closure) if source(m).exists()},
        'external_olean_hashes': {m: hashlib.sha256((ROOT/'.lake/build/lib/lean'/(m.replace('.', '/')+'.olean')).read_bytes()).hexdigest()
                                  for m in sorted(externals)
                                  if (ROOT/'.lake/build/lib/lean'/(m.replace('.', '/')+'.olean')).exists()},
        'measurements': [],
    }
    for m in selected:
        (out / (m.rsplit('.', 1)[1] + '.lean')).write_text(contents[m])
    top = ''.join(f'import {m}\n' for m in sorted(externals))
    bundle = top + '\n'
    if args.target == 'CopyoutComplete':
        bundle += '''open Lean in
run_cmd do
  if (← getEnv).contains `Xv6.WholeFunction.Copyout.compiled_copyout then
    throwError "compiled_copyout was already imported"
\n'''
    for i, m in enumerate(selected):
        bundle += f'\n/- Source: {m}; SHA256 {manifest["sources"][i]["sha256"]} -/\nsection bundle_part_{i}\n'
        body = IMPORT.sub('', contents[m])
        # Separate Lean modules may reuse a private name. Sections alone do
        # not preserve that isolation; alpha-rename private locals per source.
        private_names = re.findall(r'\bprivate\s+(?:theorem|def|abbrev|opaque|axiom|instance|structure|inductive)\s+([A-Za-z_][A-Za-z_0-9]*)', body)
        renames = {name: f'bundle_private_{i}_{name}' for name in private_names}
        manifest['sources'][i]['private_alpha_renames'] = renames
        for old, new in renames.items():
            body = re.sub(r'\b' + re.escape(old) + r'\b', new, body)
        bundle += body
        bundle += f'\nend bundle_part_{i}\n'
    if args.target == 'CopyoutComplete':
        bundle += '''\nopen Lean in
run_cmd do
  let axs ← collectAxioms ``Xv6.WholeFunction.Copyout.compiled_copyout
  if axs.contains ``sorryAx then throwError "bundled COPYOUT contains sorryAx"
  unless axs.size == 37 do throwError "Expected 37 baseline axioms; got {axs.size}"
  let baseline ← collectAxioms ``Xv6.WholeFunction.MixedAction.sound
  let extra := axs.filter fun a => !baseline.contains a
  unless extra.isEmpty do throwError "New bundled axioms: {extra}"
  logInfo "BUNDLED COPYOUT CHECKED: 37 axioms, not imported."
'''
    bundle_path = out / 'Bundle.lean'
    bundle_path.write_text(bundle)

    def measure(label, path, emit=False):
        log_path = out / (label + '.log')
        cmd = ['bash', 'Experiments/check.sh']
        if emit:
            cmd += ['-o', str(out / (label + '.olean'))]
        cmd.append(str(path.relative_to(ROOT)))
        start = time.monotonic()
        with log_path.open('w') as log:
            result = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=log)
        text = log_path.read_text()
        runtime = re.search(r'Service runtime:\s*([^\n]+)', text)
        memory = re.search(r'Memory peak:\s*([0-9.]+)([KMGT])', text)
        measurement = {
            'label': label, 'exit_code': result.returncode,
            'elapsed_including_lock_seconds': round(time.monotonic()-start, 3),
            'service_runtime': runtime[1] if runtime else None,
            'peak_mib': float(memory[1])*1024**('KMGT'.index(memory[2])-1) if memory else None,
            'log': str(log_path.relative_to(ROOT)),
        }
        manifest['measurements'].append(measurement)
        (out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
        print(json.dumps(measurement), flush=True)
        if result.returncode:
            print(text[-6000:], flush=True)
            raise SystemExit(result.returncode)

    if args.import_controls:
        ctl = out/'Imports.lean'
        ctl.write_text(top)
        measure('bundle-imports', ctl, True)
    measure('bundle', bundle_path, True)
    if args.individual:
        for module in selected:
            if source(module).read_text() != contents[module]:
                raise RuntimeError(f'Source changed since snapshot: {module}')
            # Snapshot has identical source/imports; emit elsewhere, never replace authored oleans.
            name = module.rsplit('.', 1)[1]
            measure(name, out/(name+'.lean'), True)
            if args.import_controls:
                ctl = out/(name+'Imports.lean')
                ctl.write_text(''.join(f'import {m}\n' for m in imports(contents[module])))
                measure(name+'-imports', ctl, True)
    manifest['sources_unchanged_at_end'] = all(source(m).read_text() == contents[m] for m in selected)
    manifest['external_sources_unchanged_at_end'] = all(
        hashlib.sha256(source(m).read_bytes()).hexdigest() == h
        for m, h in manifest['external_source_hashes'].items())
    manifest['external_oleans_unchanged_at_end'] = all(
        hashlib.sha256((ROOT/'.lake/build/lib/lean'/(m.replace('.', '/')+'.olean')).read_bytes()).hexdigest() == h
        for m, h in manifest['external_olean_hashes'].items())
    (out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')


if __name__ == '__main__':
    main()
