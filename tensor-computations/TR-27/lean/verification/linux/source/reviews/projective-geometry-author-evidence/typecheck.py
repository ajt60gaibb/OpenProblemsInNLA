#!/usr/bin/env python3
"""Development-only elaboration of actual projective geometry; no Challenge import."""
from pathlib import Path
import os
import subprocess

root = Path(__file__).resolve().parents[2]
lean = Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
packages = Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
build = Path('/private/tmp/nla-tr27-projective-geometry-author-build')
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build), str(root)] +
    [str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
log = Path(__file__).parent / 'development-typecheck.log'
with log.open('w') as stream:
    stream.write('Development proof elaboration with cached dependencies; not Linux Comparator verification.\n')
    stream.write(subprocess.check_output([str(lean), '--version'], text=True))
    for module in ['Definitions', 'Semantics', 'ProjectiveGeometry']:
        source = Path('NLA/TR27') / (module + '.lean')
        output = build / source.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-o', str(output), str(source)]
        stream.write('COMMAND: ' + ' '.join(command) + '\n')
        stream.flush()
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stream.write(result.stdout)
        stream.write('EXIT: ' + str(result.returncode) + '\n')
        stream.flush()
        print(module, result.returncode, result.stdout, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
