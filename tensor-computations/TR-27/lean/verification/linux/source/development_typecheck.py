#!/usr/bin/env python3
"""Development typecheck only; never substitutes for tools/lean/verify.sh.

Use the pinned Lean executable and already materialized pinned package builds.
Keep output oleans outside the source tree. Challenge's intentional specification
placeholders are expected warnings, never proof evidence.
"""
from pathlib import Path
import argparse
import os
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    build = args.build_dir.resolve()
    if build.is_relative_to(root):
        parser.error('Use a build directory outside the retained source tree')
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(
        [str(build), str(root)] +
        [str(p / '.lake/build/lib/lean') for p in sorted(args.packages.resolve().iterdir())
         if p.is_dir()])
    files = ['NLA/TR27/Definitions.lean', 'Challenge.lean']
    log_name = 'statement-typecheck.log'
    log = root / 'reviews' / log_name
    log.parent.mkdir(exist_ok=True)
    with log.open('w') as stream:
        stream.write('Development-only typecheck; not authoritative Linux verification.\n')
        version = subprocess.check_output([str(args.lean), '--version'], text=True)
        stream.write(version)
        for file in files:
            output = build / Path(file).with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [str(args.lean), '-o', str(output), file]
            stream.write('COMMAND: ' + ' '.join(command) + '\n')
            stream.flush()
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            stream.write(result.stdout)
            stream.write('EXIT: ' + str(result.returncode) + '\n')
            stream.flush()
            print(file, result.returncode, result.stdout, flush=True)
            if result.returncode:
                raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
