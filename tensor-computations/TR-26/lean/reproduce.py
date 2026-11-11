#!/usr/bin/env python3
"""Replay the exact TR-26 full Target locally; no Linux Comparator claim.

Requires the pinned Lean executable and already materialized pinned Lake
packages. Package sources are read-only. Fresh compiled objects are removed;
raw logs, source hashes, version and dependency checks go to --output.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    project = Path(__file__).resolve().parent
    lean = args.lean.resolve()
    packages = args.packages.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    result = {'scope': 'Local source replay of both literal endpoints and full Target; no final package or Linux claim',
              'whole_problem_verified': False, 'linux_isolation': False,
              'comparator_executed': False, 'raw_kernel_replay': False,
              'commands': [], 'pass': False}

    def dependencies() -> list:
        reports = []
        for package in manifest['packages']:
            path = packages / package['name']
            revision = subprocess.check_output(
                ['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            status = subprocess.check_output(
                ['git', '-C', str(path), 'status', '--porcelain',
                 '--untracked-files=no'], text=True)
            reports.append({'name': package['name'], 'revision': revision,
                            'expected_revision': package['rev'],
                            'tracked_status': status})
            if revision != package['rev'] or status:
                raise RuntimeError('Pinned package revision/cleanliness mismatch: ' + str(path))
        return reports

    try:
        result['lean_version'] = subprocess.check_output([str(lean), '--version'], text=True)
        if 'version 4.33.1,' not in result['lean_version']:
            raise RuntimeError('Expected pinned Lean 4.33.1')
        result['lean_executable_sha256'] = sha(lean)
        result['dependencies_before'] = dependencies()
        lock = json.loads((project / 'PACKAGE_LOCK.json').read_text())
        for name, entry in lock['files'].items():
            if sha(project / name) != entry['sha256']:
                raise RuntimeError('Package source lock mismatch: ' + name)
        files = ['NLA/Statements/Infrastructure.lean', 'NLA/Statements/TR26.lean', 'NLA/Proofs/TR26/ConormalLemmas.lean', 'NLA/Proofs/TR26/LocalConormal.lean', 'NLA/Proofs/TR26/AnalyticConormal.lean', 'NLA/Proofs/TR26/BinaryDefinitions.lean', 'NLA/Proofs/TR26/Denominator.lean', 'NLA/Proofs/TR26/Numerator.lean', 'NLA/Proofs/TR26/Wronskian.lean', 'NLA/Proofs/TR26/BinaryScaling.lean', 'NLA/Proofs/TR26/IncidenceIdeal.lean', 'NLA/Proofs/TR26/IncidenceScaling.lean', 'NLA/Proofs/TR26/TangentRank.lean', 'NLA/Proofs/TR26/LinearCriticalGraph.lean', 'NLA/Proofs/TR26/ChartIncidence.lean', 'NLA/Proofs/TR26/SeparablePencil.lean', 'NLA/Proofs/TR26/WronskianPencilDegree.lean', 'NLA/Proofs/TR26/WronskianJets.lean', 'NLA/Proofs/TR26/WronskianJetParameterization.lean', 'NLA/Proofs/TR26/ClearedJetGraph.lean', 'NLA/Proofs/TR26/CommonFactorWronskian.lean', 'NLA/Proofs/TR26/CommonRootWronskian.lean', 'NLA/Proofs/TR26/FixedDiscriminant.lean', 'NLA/Proofs/TR26/FixedDiscriminantNonzero.lean', 'NLA/Proofs/TR26/FixedDiscriminantRoots.lean', 'NLA/Proofs/TR26/FixedDiscriminantBinary.lean', 'NLA/Proofs/TR26/FixedDiscriminantResultant.lean', 'NLA/Proofs/TR26/FixedDiscriminantSpecialization.lean', 'NLA/Proofs/TR26/IsotropicFactor.lean', 'NLA/Proofs/TR26/FamilyDiscriminant.lean', 'NLA/Proofs/TR26/FamilyDiscriminantEvaluation.lean', 'NLA/Proofs/TR26/WronskianPencil.lean', 'NLA/Proofs/TR26/FamilyDiscriminantNonzero.lean', 'NLA/Proofs/TR26/IsotropicDivisibility.lean', 'NLA/Proofs/TR26/IsotropicFamilyFactor.lean', 'NLA/Proofs/TR26/HomogeneousQuotient.lean', 'NLA/Proofs/TR26/ComplementaryFactor.lean', 'NLA/Proofs/TR26/SeparablePencilAvoid.lean', 'NLA/Proofs/TR26/MatrixJetImage.lean', 'NLA/Proofs/TR26/PolynomialImageIdeal.lean', 'NLA/Proofs/TR26/FiniteJetPrimeImage.lean', 'NLA/Proofs/TR26/FiniteJetFactorLemmas.lean', 'NLA/Proofs/TR26/NonisotropicDoubleWitness.lean', 'NLA/Proofs/TR26/IsotropicWronskianWitness.lean', 'NLA/Proofs/TR26/FixedDiscriminantAffine.lean', 'NLA/Proofs/TR26/DiscriminantProduct.lean', 'NLA/Proofs/TR26/DoubleRootSplitVariation.lean', 'NLA/Proofs/TR26/FixedDiscriminantVariation.lean', 'NLA/Proofs/TR26/OrdinaryDoubleRootVariation.lean', 'NLA/Proofs/TR26/WronskianLinear.lean', 'NLA/Proofs/TR26/IsotropicTransverseWitness.lean', 'NLA/Proofs/TR26/NonisotropicTransverseWitness.lean', 'NLA/Proofs/TR26/IsotropicMultiplicity.lean', 'NLA/Proofs/TR26/NonisotropicMultiplicity.lean', 'NLA/Proofs/TR26/PrimeHypersurfaceFactor.lean', 'NLA/Proofs/TR26/ComplementaryIrreducible.lean', 'NLA/Proofs/TR26/CurveEquations.lean', 'NLA/Proofs/TR26/CriticalEquation.lean', 'NLA/Proofs/TR26/CurveNormalRank.lean', 'NLA/Proofs/TR26/CurveDifferentiation.lean', 'NLA/Proofs/TR26/WronskianBinaryLinear.lean', 'NLA/Proofs/TR26/WronskianCharts.lean', 'NLA/Proofs/TR26/ReverseWronskianCharts.lean', 'NLA/Proofs/TR26/CriticalEquationDerivative.lean', 'NLA/Proofs/TR26/CurveChartCover.lean', 'NLA/Proofs/TR26/ReverseCurveNormalRank.lean', 'NLA/Proofs/TR26/RamificationCharts.lean', 'NLA/Proofs/TR26/IsotropicChartCover.lean', 'NLA/Proofs/TR26/ProjectiveRamification.lean', 'NLA/Proofs/TR26/IsotropicImageContainment.lean', 'NLA/Proofs/TR26/IsotropicDegree.lean', 'NLA/Proofs/TR26/DiscriminantImageBounds.lean', 'NLA/Proofs/TR26/FiniteProjectiveCharts.lean', 'NLA/Proofs/TR26/MatrixReversal.lean', 'NLA/Proofs/TR26/FiniteProjectiveDensity.lean', 'NLA/Proofs/TR26/ProjectiveHypersurfaceClosure.lean', 'NLA/Proofs/TR26/NonisotropicAssembly.lean', 'NLA/Proofs/TR26/NonisotropicDegree.lean', 'NLA/Proofs/TR26/MainTarget.lean', 'Reviewed/TR26.lean', 'Challenge.lean', 'Solution.lean', 'EndpointAudit.lean', 'Identity.lean']
        with tempfile.TemporaryDirectory(prefix='nla-tr26-full-local-replay-') as temporary:
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join(
                [temporary] + [str(packages / p['name'] / '.lake/build/lib/lean')
                               for p in manifest['packages']] +
                [str(lean.parent.parent / 'lib/lean')])
            for name in files:
                source = project / name
                artifact = Path(temporary) / Path(name).with_suffix('.olean')
                artifact.parent.mkdir(parents=True, exist_ok=True)
                before = sha(source)
                command = [str(lean), '-R', str(project), '-o', str(artifact), str(source)]
                process = subprocess.run(command, env=env, cwd=project,
                                         capture_output=True, text=True, timeout=300)
                log = output / (name.replace('/', '-') + '.log')
                log.write_text(process.stdout + process.stderr)
                result['commands'].append({'source': name, 'source_sha256': before,
                                           'argv': command, 'exit_code': process.returncode,
                                           'log': log.name, 'log_sha256': sha(log)})
                print(name, process.returncode, flush=True)
                if process.returncode or sha(source) != before:
                    raise RuntimeError('Source compilation or immutability failed: ' + name)
            controls = [('ChallengeTrustRejection', 'sorryAx'),
                        ('DefinitionKindRejection', 'requires an actual theorem'),
                        ('CustomAxiomRejection', 'PackageOracle')]
            control_root = Path(temporary) / 'control-sources'
            control_root.mkdir()
            for name, diagnostic in controls:
                stored = project / 'controls' / (name + '.lean.txt')
                source = control_root / (name + '.lean')
                source.write_bytes(stored.read_bytes())
                command = [str(lean), '-R', str(control_root), '-o',
                           str(Path(temporary) / (name + '.olean')), str(source)]
                process = subprocess.run(command, env=env, cwd=control_root,
                                         capture_output=True, text=True, timeout=300)
                log = output / (name + '.log')
                log.write_text(process.stdout + process.stderr)
                accepted = process.returncode != 0 and diagnostic in log.read_text()
                result['commands'].append({'source': str(stored.relative_to(project)),
                                           'source_sha256': sha(stored), 'argv': command,
                                           'exit_code': process.returncode,
                                           'expected_exit': 'nonzero', 'expected_diagnostic': diagnostic,
                                           'rejection_control_pass': accepted,
                                           'log': log.name, 'log_sha256': sha(log)})
                print(name, 'EXPECTED_REJECTION' if accepted else 'FAIL', flush=True)
                if not accepted:
                    raise RuntimeError('Expected rejection control failed: ' + name)
            result['rejection_controls_passed'] = len(controls)
        result['temporary_compiled_objects_removed'] = True
        result['dependencies_after'] = dependencies()
        result['pass'] = True
    except Exception as error:
        result['error'] = str(error)
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return 0 if result['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
