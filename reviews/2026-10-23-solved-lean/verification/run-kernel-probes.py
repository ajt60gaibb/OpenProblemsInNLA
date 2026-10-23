#!/usr/bin/env python3
"""Local LeanCert controls; no NLA proof or isolated Linux verification claim.

Adapted from the October 17 runtime probe. Dependencies remain read-only. An
optional numerical-tactic rebuild writes exclusively into an owned temp tree.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.file_digest(Path(path).open('rb'), 'sha256').hexdigest()

def capture(argv, **kwargs):
    started = time.monotonic()
    cp = subprocess.run(list(map(str, argv)), capture_output=True, text=True, **kwargs)
    return {'argv': list(map(str, argv)), 'exit_code': cp.returncode,
            'stdout': cp.stdout, 'stderr': cp.stderr,
            'elapsed_seconds': time.monotonic() - started}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--packages', type=Path, required=True)
    ap.add_argument('--build-numerical', action='store_true')
    args = ap.parse_args()
    lean, packages = args.lean.resolve(), args.packages.resolve()
    attempt = Path(tempfile.mkdtemp(prefix='attempt-', dir=HERE / 'kernel-probes'))
    source = attempt / 'source'
    source.mkdir()
    build = Path(tempfile.mkdtemp(prefix='nla-oct23-kernel-'))
    manifest = json.loads((HERE / 'published-tooling/lean-statements/lake-manifest.json').read_text())
    result = {'scope': __doc__, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'platform': platform.platform(), 'baseline': (HERE/'baseline.txt').read_text().strip(),
              'script_sha256': sha(__file__), 'commands': [], 'checks': {}, 'pass': False,
              'nla_targets_proved': False, 'authoritative_linux_sandbox': False,
              'full_comparator_executed': False, 'raw_kernel_replay_executed': False,
              'numerical_tactic_rebuilt': False, 'temporary_build_directory': str(build)}
    def deps():
        out = []
        for p in manifest['packages']:
            directory = packages / p['name']
            head = capture(['git','-C',directory,'rev-parse','HEAD'])
            status = capture(['git','-C',directory,'status','--porcelain','--untracked-files=no'])
            ok = head['exit_code'] == status['exit_code'] == 0 and head['stdout'].strip() == p['rev'] and not status['stdout'].strip()
            out.append({'name':p['name'], 'expected':p['rev'], 'directory':str(directory), 'head':head, 'status':status, 'ok':ok})
        if not all(p['ok'] for p in out):
            raise RuntimeError('dependency pins or tracked-source cleanliness failed')
        return out
    env = os.environ.copy()
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH','')
    env['LEAN_PATH'] = os.pathsep.join([str(build)] + [str(packages/p['name']/'.lake/build/lib/lean') for p in manifest['packages']] + [str(lean.parent.parent/'lib/lean')])
    def run(name, content, expected=0, markers=()):
        path = source / (name+'.lean')
        path.write_text(content)
        rec = capture([lean, '-R', source, '-o', build/(name+'.olean'), path], cwd=source, env=env, timeout=180)
        log = attempt/(name+'.log')
        log.write_text(rec['stdout']+rec['stderr'])
        rec.update(name=name, source_sha256=sha(path), log_sha256=sha(log))
        result['commands'].append(rec)
        text = rec['stdout']+rec['stderr']
        ok = (rec['exit_code'] == expected if expected == 0 else rec['exit_code'] != 0) and all(m in text for m in markers)
        result['checks'][name] = ok
        print(name, 'PASS' if ok else 'FAIL', flush=True)
        if not ok:
            raise RuntimeError('unexpected control outcome: '+name)
    try:
        version = capture([lean,'--version'])
        result.update(lean_version=version, lean_executable_sha256=sha(lean), dependencies_before=deps())
        if version['exit_code'] or 'version 4.33.1,' not in version['stdout']:
            raise RuntimeError('expected pinned Lean 4.33.1')
        prefix = 'import Mathlib.Tactic\nimport LeanCert.Tactic.Verification\nset_option leancert.trust "kernel"\n'
        run('KernelPositive', prefix+'theorem probe : (2 : ℚ) / 3 + 1 / 3 = 1 := by norm_num\n#assert_trust kernel probe\n#print axioms probe\n', markers=('propext','Quot.sound'))
        run('RejectSorry', prefix+'theorem probe : True := by sorry\n#print axioms probe\n#assert_trust kernel probe\n', 1, ('sorryAx',))
        run('RejectNative', prefix+'theorem probe : (List.range 37).reverse.length = 37 := by native_decide\n#print axioms probe\n#assert_trust kernel probe\n', 1, ('native_decide.ax',))
        spec = importlib.util.spec_from_file_location('published_harness', HERE/'published-tooling/tools/lean/harness.py')
        import sys
        sys.path.insert(0,str(HERE/'published-tooling/tools/lean'))
        harness = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(harness)
        run('DefinedTarget', 'import Mathlib.Tactic\ndef target : Prop := False\n')
        generated = harness.proof_trust_source({'solution_module':'DefinedTarget','theorem_names':['target']})
        run('RejectDefinitionExport', generated, 1, ('expected a proved theorem constant',))
        blocked = capture(['python3',HERE/'published-tooling/tools/lean/harness.py','selftest',build/'linux-tools'],timeout=30)
        result['linux_precondition_control'] = blocked
        result['checks']['LinuxFailClosed'] = blocked['exit_code'] == 2 and 'requires Linux' in blocked['stderr']
        if args.build_numerical:
            graph = {}
            lc = packages/'leancert'
            def header_imports(text):
                # Lean imports occur in the module header. Documentation can
                # contain import examples (including apparent self-imports).
                # Remove nested block comments, then stop at the first command.
                clean = []
                depth = 0
                i = 0
                while i < len(text):
                    pair = text[i:i+2]
                    if pair == '/-':
                        depth += 1
                        i += 2
                    elif depth and pair == '-/':
                        depth -= 1
                        i += 2
                    else:
                        if not depth or text[i] == '\n':
                            clean.append(text[i])
                        i += 1
                imports = []
                for line in ''.join(clean).splitlines():
                    line = line.split('--',1)[0].strip()
                    if not line or line == 'prelude':
                        continue
                    if not line.startswith('import '):
                        break
                    imports.extend(line.removeprefix('import ').split())
                return imports
            def visit(module):
                if module in graph:
                    return
                path = lc/Path(*module.split('.')).with_suffix('.lean')
                if not path.is_file():
                    raise RuntimeError('missing pinned source '+module)
                imports = header_imports(path.read_text())
                # Build the entire LeanCert prefix. A locally present prefix
                # shadows its cached counterpart during Lean import lookup.
                graph[module] = [m for m in imports if m.startswith('LeanCert.')]
                for dep in graph[module]:
                    visit(dep)
            visit('LeanCert.Tactic.LeanCert')
            result['numerical_build_sources'] = {}
            for module in graph:
                rel = Path(*module.split('.')).with_suffix('.lean')
                dest = source/rel
                dest.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(lc/rel,dest)
                result['numerical_build_sources'][module] = {'sha256':sha(dest),'bytes':dest.stat().st_size}
            shutil.copyfile(lc/'LICENSE',source/'LICENSE-LEANCERT')
            def compile_module(module):
                rel = Path(*module.split('.')).with_suffix('.lean')
                output = build/rel.with_suffix('.olean')
                output.parent.mkdir(parents=True,exist_ok=True)
                rec = capture([lean,'-R',source,'-o',output,source/rel],cwd=source,env=env,timeout=600)
                rec['module'] = module
                log = attempt/(module+'.log')
                log.write_text(rec['stdout']+rec['stderr'])
                rec['log_sha256'] = sha(log)
                return rec
            complete = set()
            pending = set(graph)
            active = {}
            with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
                while pending or active:
                    for module in sorted(pending):
                        if len(active) >= 3:
                            break
                        if set(graph[module]) <= complete:
                            active[pool.submit(compile_module,module)] = module
                    pending -= set(active.values())
                    if not active:
                        raise RuntimeError('cycle in numerical build imports')
                    done,_ = concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
                    for future in done:
                        module = active.pop(future)
                        rec = future.result()
                        result['commands'].append(rec)
                        if rec['exit_code']:
                            raise RuntimeError('numerical dependency build failed: '+module)
                        complete.add(module)
                        print('built',len(complete),'/',len(graph),module,flush=True)
            result['numerical_tactic_rebuilt'] = True
            run('NumericalKernel', 'import LeanCert.Tactic.LeanCert\nimport LeanCert.Tactic.Verification\nset_option leancert.trust "kernel"\ntheorem numericProbe : Real.log 2 < (7 : ℝ) / 10 := by\n  leancert (trust := kernel)\n#assert_trust kernel numericProbe\n#print axioms numericProbe\n',markers=('propext','Quot.sound'))
        result['pass'] = all(result['checks'].values())
    except Exception as error:
        result['error'] = str(error)
    finally:
        result['dependencies_after'] = deps()
        result['snapshot_sha256'] = {str(p.relative_to(source)):sha(p) for p in source.rglob('*') if p.is_file()}
        shutil.rmtree(build)
        result['temporary_compiled_objects_removed'] = not build.exists()
        (attempt/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        (HERE/'kernel-probes/latest.json').write_text(json.dumps({'attempt':attempt.name,'result_sha256':sha(attempt/'result.json')},indent=2)+'\n')
        print(json.dumps({'attempt':str(attempt),'pass':result['pass'],'error':result.get('error')}),flush=True)
    return 0 if result['pass'] else 1

if __name__ == '__main__':
    (HERE/'kernel-probes').mkdir(exist_ok=True)
    raise SystemExit(main())
