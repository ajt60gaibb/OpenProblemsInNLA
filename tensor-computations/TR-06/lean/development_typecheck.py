#!/usr/bin/env python3
"""Elaborate only the TR-06 statement draft using a prebuilt local package cache.

This is not a Lake build, a proof check, or authoritative Linux Comparator
verification. In particular, the deliberately sorry-filled Challenge proves no
mathematics. Never use this script as a replacement for tools/lean/verify.sh.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--evidence-dir', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    build = args.build_dir.resolve()
    evidence = args.evidence_dir.resolve()
    if build.is_relative_to(root):
        parser.error('Compiled outputs must be outside the retained source tree')
    evidence.mkdir(parents=True, exist_ok=True)
    files = ['NLA/TR06/Definitions.lean', 'Challenge.lean']
    env = os.environ.copy()
    packages = args.packages.resolve()
    env['LEAN_PATH'] = os.pathsep.join(
        [str(build), str(root)] +
        [str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
    receipt = {
        'scope': 'Development statement elaboration only; Challenge placeholders prove nothing.',
        'authoritative_linux_verification': False,
        'command': sys.argv,
        'lean_version': subprocess.check_output([str(args.lean), '--version'], text=True).strip(),
        'inputs': {f: sha256(root / f) for f in files},
        'package_git_heads': {},
        'checks': [],
    }
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        path = packages / package['name']
        if not path.exists():
            receipt['package_git_heads'][package['name']] = {'available': False}
            continue
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        receipt['package_git_heads'][package['name']] = {
            'available': True, 'head': head, 'matches_pin': head == package['rev']}
        if head != package['rev']:
            parser.error(f'Package {package["name"]} differs from committed pin')
    code = 0
    for file in files:
        output = build / Path(file).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(args.lean), '-o', str(output), file]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = evidence / (file.replace('/', '-') + '.log')
        log.write_text('COMMAND: ' + ' '.join(command) + '\n' + result.stdout +
                       f'EXIT: {result.returncode}\n')
        receipt['checks'].append({'file': file, 'exit_code': result.returncode,
                                  'log': log.name, 'sha256': sha256(log)})
        print(file, result.returncode, result.stdout, flush=True)
        if result.returncode:
            code = result.returncode
            break
    receipt['inputs_unchanged'] = all(sha256(root / f) == h for f, h in receipt['inputs'].items())
    receipt['elaboration_passed'] = code == 0 and receipt['inputs_unchanged']
    (evidence / 'statement-elaboration.json').write_text(json.dumps(receipt, indent=2) + '\n')
    raise SystemExit(code if receipt['inputs_unchanged'] else 1)


if __name__ == '__main__':
    main()
