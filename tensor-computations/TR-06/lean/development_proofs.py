#!/usr/bin/env python3
"""Check incomplete TR-06 proof modules against pinned, prebuilt local libraries.

This development check is not an authoritative Linux build, Comparator run,
independent kernel replay, or a proof of the complete TR-06 target. It cannot
replace tools/lean/verify.sh. Cached dependency artifacts are reused.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--leancert', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--evidence-dir', type=Path, required=True)
    parser.add_argument('--modules', nargs='+', default=[
        'Generic', 'LinearNorm', 'MetricSlope', 'Radial', 'PolynomialNull',
        'Homogeneity', 'Measurability', 'RankOneCharts', 'LocusMeasurability',
        'SourceBridge', 'AngularMeasurability', 'NormDet', 'Rectangular', 'LocalVolume', 'Density', 'Radius', 'Area', 'WeightedArea', 'FiniteVolume',
        'NullImage', 'GraphJacobian', 'Complexification', 'ClosedFibers', 'AlgebraFiber',
        'ProjectionAtlasDefinitions', 'ProjectionLinear', 'ProjectionCompact',
        'ProjectionTangent', 'ProjectionLocal', 'ProjectionAtlas',
        'QuasiFiniteCharactersDefinitions', 'QuasiFiniteCharacters'])
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    build, evidence = args.build_dir.resolve(), args.evidence_dir.resolve()
    if build.is_relative_to(root):
        parser.error('Compiled outputs must be outside the retained source tree')
    if any(not m.isidentifier() for m in args.modules):
        parser.error('Modules must be simple names below NLA.TR06')
    files = ['NLA/TR06/Definitions.lean'] + [f'NLA/TR06/{m}.lean' for m in args.modules]
    inputs = {f: digest(root/f) for f in files}
    manifest = json.loads((root/'lake-manifest.json').read_text())
    packages, leancert = args.packages.resolve(), args.leancert.resolve()
    package_records, paths = {}, []
    for package in manifest['packages']:
        path = leancert if package['name'] == 'leancert' else packages/package['name']
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                        cwd=path, text=True)
        package_records[package['name']] = {'head': head, 'matches_pin': head == package['rev'],
                                             'tracked_source_clean': not dirty}
        if head != package['rev'] or dirty:
            parser.error(f'Package {package["name"]} has unpinned or modified tracked source')
        paths.append(str(path/'.lake/build/lib/lean'))
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(build), str(root), *paths])
    receipt = {'scope': __doc__, 'authoritative_linux_verification': False,
               'comparator_run': False, 'command': sys.argv,
               'lean_version': subprocess.check_output([str(args.lean), '--version'], text=True).strip(),
               'lean_binary_sha256': digest(args.lean), 'inputs': inputs,
               'packages': package_records, 'checks': []}
    evidence.mkdir(parents=True, exist_ok=True)
    code = 0
    for file in files:
        output = build/Path(file).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(args.lean), '-o', str(output), file]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = evidence/(file.replace('/', '-')+'.log')
        log.write_text('COMMAND: '+' '.join(command)+'\n'+result.stdout+f'EXIT: {result.returncode}\n')
        receipt['checks'].append({'file': file, 'exit_code': result.returncode,
                                  'log': log.name, 'log_sha256': digest(log)})
        print(file, result.returncode, result.stdout, flush=True)
        if result.returncode:
            code = result.returncode
            break
    receipt['inputs_unchanged'] = all(digest(root/f) == h for f,h in inputs.items())
    receipt['local_elaboration_passed'] = code == 0 and receipt['inputs_unchanged']
    (evidence/'development-proof-check.json').write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(code if receipt['inputs_unchanged'] else 1)


if __name__ == '__main__':
    main()
