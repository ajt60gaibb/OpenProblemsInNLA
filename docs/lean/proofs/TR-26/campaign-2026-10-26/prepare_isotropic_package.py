#!/usr/bin/env python3
"""Prepare the partial TR-26 isotropic package from a frozen Git checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

SOURCE_REF = '4692336f0e1a50d5e261bba68277875da30fba51'
CAMPAIGN = 'docs/lean/proofs/TR-26/campaign-2026-10-26'
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--template', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--reviews-root', type=Path)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)

    def git(path):
        return subprocess.check_output(['git', 'show', f'{SOURCE_REF}:{path}'], cwd=args.repo)

    def write(path, content):
        p = out / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(content if isinstance(content, bytes) else content.encode())

    def js(path, obj):
        write(path, json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

    cp = json.loads(git(f'{CAMPAIGN}/ISOTROPIC_ENDPOINT_CHECKPOINT.json'))
    copies = []

    def copy(path, target):
        data = git(path)
        write(target, data)
        copies.append({'path': target, 'source_path': path, 'source_ref': SOURCE_REF,
                       'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})

    for rec in cp['proof_inputs']:
        copy(rec['path'], rec['path'].removeprefix('lean-statements/'))
    for name in ['NLA/Statements/Infrastructure.lean', 'NLA/Statements/TR26.lean', 'Reviewed/TR26.lean']:
        copy('lean-statements/' + name, name)
    copy('tensor-computations/TR-26/README.md', 'sources/ORIGINAL.md')
    copy('docs/lean/statements/TR-26/NUMERICAL_TARGETS.md', 'sources/NUMERICAL_TARGETS.md')
    for suffix in ['md', 'tex', 'pdf']:
        copy(f'references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.{suffix}', f'sources/TR-26.{suffix}')
    copy(f'{CAMPAIGN}/ISOTROPIC_ENDPOINT_CHECKPOINT.json', 'reviews/ISOTROPIC_ENDPOINT_CHECKPOINT.json')
    copy(f'{CAMPAIGN}/isotropic-endpoint-author-acceptances.json', 'reviews/isotropic-endpoint-author-acceptances.json')
    prefix = f'{CAMPAIGN}/preproof/'
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', SOURCE_REF, '--', prefix],
                                    cwd=args.repo, text=True).splitlines()
    for path in paths:
        target = 'reviews/preproof/' + path.removeprefix(prefix)
        if target.endswith('.lean'):
            target += '.txt'
        copy(path, target)
    copy('lean-statements/lean-toolchain', 'lean-toolchain')
    manifest = json.loads((args.template / 'lake-manifest.json').read_text())
    manifest['name'] = 'NLATR26Isotropic'
    js('lake-manifest.json', manifest)
    write('lakefile.toml', '''name = "NLATR26Isotropic"
version = "0.1.0"
defaultTargets = ["Solution", "EndpointAudit", "Identity"]

[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "621a43d7cf21f87872392a01e874f2f1dbddc926"

[[lean_lib]]
name = "NLA"
globs = ["NLA.Statements.+", "NLA.Proofs.TR26.+"]

[[lean_lib]]
name = "Reviewed"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "EndpointAudit"

[[lean_lib]]
name = "Identity"
''')
    write('Challenge.lean', '''import NLA.Statements.TR26
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR26
theorem isotropic_degree (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d)
      (NLA.Statements.TR26.IsotropicImage d) := by
  sorry
end NLA.Proofs.TR26
''')
    write('Solution.lean', '''import NLA.Proofs.TR26.IsotropicDegree

/-! One literal endpoint only. The nonisotropic endpoint and full Target
remain unproved and are not selected as Comparator exports. -/
set_option leancert.trust "kernel"
''')
    write('Identity.lean', '''import NLA.Statements.TR26
import Reviewed.TR26
set_option leancert.trust "kernel"
/-! Frozen statement identity, not a proof of the full Target. -/
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
''')
    write('EndpointAudit.lean', '''import Solution
import Reviewed.TR26
set_option leancert.trust "kernel"
open Lean Elab Command
elab "#package_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo name with
  | .thmInfo _ => pure ()
  | _ => throwError "package requires an actual theorem: {name}"
elab "#package_absent " target:ident : command => do
  if (← getEnv).contains target.getId then
    throwError "partial package unexpectedly contains {target.getId}"
#package_theorem NLA.Proofs.TR26.isotropic_degree
#package_absent NLA.Proofs.TR26.nonisotropic_degree
#package_absent NLA.Proofs.TR26.target
#assert_trust kernel NLA.Proofs.TR26.isotropic_degree
#print axioms NLA.Proofs.TR26.isotropic_degree
example (d : ℕ) (hd : 2 ≤ d) : NLA.Statements.TR26.HasReducedDegree d (2*d)
    (NLA.Statements.TR26.IsotropicImage d) := NLA.Proofs.TR26.isotropic_degree d hd
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
''')
    write('controls/ChallengeTrustRejection.lean.txt', '''import Challenge
#assert_trust kernel NLA.Proofs.TR26.isotropic_degree
''')
    write('controls/DefinitionKindRejection.lean.txt', '''import EndpointAudit
def FakeIsotropicEndpoint (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d)
      (NLA.Statements.TR26.IsotropicImage d) := NLA.Proofs.TR26.isotropic_degree d hd
#package_theorem FakeIsotropicEndpoint
''')
    write('controls/CustomAxiomRejection.lean.txt', '''import EndpointAudit
axiom PackageOracle (d : ℕ) (hd : 2 ≤ d) :
  NLA.Statements.TR26.HasReducedDegree d (2*d) (NLA.Statements.TR26.IsotropicImage d)
theorem OracleEndpoint (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d)
      (NLA.Statements.TR26.IsotropicImage d) := PackageOracle d hd
#assert_trust kernel OracleEndpoint
''')
    js('comparator.json', {'challenge_module': 'Challenge', 'solution_module': 'Solution',
                          'theorem_names': ['NLA.Proofs.TR26.isotropic_degree'],
                          'definition_names': [], 'permitted_axioms': AXIOMS})
    js('SOURCE_MAP.json', {'scope': 'One complete isotropic endpoint, full problem remains Solved',
                           'proof_source_ref': SOURCE_REF, 'copies': copies})
    js('formalization.yaml', {
        'version': 'v0.4',
        'project': {'name': 'TR-26: exact reduced isotropic degree',
                    'description': 'The complete raw isotropic-image endpoint for all d>=2. The nonisotropic closure endpoint and full Target remain unproved.',
                    'authors': ['OpenAI Codex AI agents /root, /root/proof_route and /root/ie22_sampling (formalization); independent AI-agent endpoint/package review pending'],
                    'license': 'No licence grant is made by this metadata.'},
        'sources': [
            {'title': 'TR-26 retained original mathematical target', 'id': 'sources/ORIGINAL.md', 'type': 'web-post', 'relationship': 'formalizes'},
            {'title': 'Degrees of the two Rayleigh–Ritz discriminant parts for rational normal curves',
             'authors': ['Matthew J. Colbrook'], 'id': 'sources/TR-26.tex', 'type': 'manuscript',
             'relationship': 'formalizes', 'location': 'Isotropic part of Theorem 1; fixed unweighted and bilinear model',
             'note': 'Mathematical source credit retained. AI-agent implementation and review imply no external human endorsement.'}],
        'automation': {'methods': [{'method': 'agent', 'framework': 'OpenAI Codex',
                                    'tool_setup': 'Pinned Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926.',
                                    'prompting_notes': 'Two independent exact pre-proof approvals preceded implementation; preserve the full original Target and distinguish the one proved endpoint.'}],
                       'notes': 'LeanCert kernel mode. All algebraic and analytic proofs are kernel-checked; no numerical certificate is required.'},
        'status': {'phase': 'support-only', 'scope': 'Complete exact isotropic reduced-degree endpoint only, including full-ideal raw image equality, d=2, infinity, zero numerator and numerator-kernel matrices.',
                   'whole_problem_verified': False, 'canonical_status': 'Solved', 'sorry_count': 0,
                   'sorry_in_definitions': 0, 'axioms': AXIOMS,
                   'main_results': [{'declaration': 'NLA.Proofs.TR26.isotropic_degree',
                                     'file': 'NLA/Proofs/TR26/IsotropicDegree.lean', 'sorry_count': 0,
                                     'axioms': AXIOMS, 'comparator_config': 'comparator.json',
                                     'verification_status': 'Author LeanCert kernel build passes; independent endpoint/package review and isolated Linux verification pending.'}]},
        'fidelity': {'divergences': 'The isotropic endpoint is literal. The nonisotropic endpoint, full Target, reduced complementary factor and full problem verification are not claimed.'},
        'review': {'status': 'Two independent pre-proof approvals; final independent endpoint/package reviews pending',
                   'reviewers': ['/root/inventory (pre-proof)', '/root/verification (pre-proof and support)'],
                   'notes': 'Retained pre-proof approvals concern both exact endpoints. Support reviews do not approve the later endpoint; no Linux/Comparator acceptance is claimed yet.'},
        'acknowledgements': 'Matthew J. Colbrook retains source mathematical credit. Original references and authorship/provenance records are preserved. Mathlib and LeanCert APIs are reused.'})
    write('README.md', '''# TR-26 isotropic endpoint

This package proves exactly `NLA.Proofs.TR26.isotropic_degree`: for every d≥2, the unchanged raw `IsotropicImage d` has `HasReducedDegree d (2*d)`. It uses the full original vanishing ideal and its entire z-Jacobian space, the fixed unweighted Veronese curve, independent complex symmetric-matrix coordinates and bilinear pairings. Infinity, the matrix-to-numerator kernel, zero numerator and numerator proportional to the denominator are included.

The nonisotropic reduced-degree endpoint and full `Target` remain unproved. TR-26 remains **Solved**. `Identity.lean` checks the frozen original full statement only; it does not prove it. Comparator selects the actual isotropic theorem and no replaceable definition holes. The challenge contains its one intentional reference hole and is never imported by Solution; the original three-endpoint reference is retained as text under reviews/preproof.

The 33 proof sources and three statement/identity inputs are byte-exact copies from source checkpoint `4692336f0e1a50d5e261bba68277875da30fba51`; `SOURCE_MAP.json` records every source and hash. Complete originals, manuscript and pre-proof reviews are retained. Source mathematical credit remains with Matthew J. Colbrook; formal implementation and reviews are AI-agent work, with no external human endorsement or new licence grant claimed.

Author macOS LeanCert kernel acceptance is established. Independent endpoint/package review and authentic isolated Linux Comparator/raw-kernel receipts are still pending for this package. No such receipt is implied by a local build.

Run `python3 reproduce.py --lean /absolute/path/to/pinned/lean --packages /absolute/path/to/pinned/packages --output /new/empty/output/path` for a fresh local replay. The project pins Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926. The repository's unchanged `tools/lean/verify.sh` supplies the separate Linux isolation, actual theorem-kind/axiom checks, Comparator and raw-kernel replay.
''')
    # Retain the established fresh-object replay implementation and replace
    # its explicit source list with the topologically ordered package closure.
    replay = (args.template / 'reproduce.py').read_text()
    replay = replay.replace('eleven RA-05 support exports', 'one TR-26 isotropic endpoint')
    replay = replay.replace('Local source replay of eleven support theorems only', 'Local source replay of the literal isotropic endpoint only')
    replay = replay.replace('nla-ra05-local-replay-', 'nla-tr26-isotropic-local-replay-')
    source_paths = {x['path'] for x in copies if x['path'].endswith('.lean')}
    graph = {}
    for name in source_paths:
        imports = []
        for line in (out / name).read_text().splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    dep = module.replace('.', '/') + '.lean'
                    if dep in source_paths:
                        imports.append(dep)
        graph[name] = imports
    ordered, active = [], set()

    def visit(name):
        if name in ordered:
            return
        if name in active:
            raise RuntimeError('Import cycle: ' + name)
        active.add(name)
        for dep in graph[name]:
            visit(dep)
        active.remove(name)
        ordered.append(name)

    for name in sorted(source_paths):
        visit(name)
    start = replay.index("        files = ['NLA/Statements/Infrastructure.lean'")
    end = replay.index('\n        with tempfile.TemporaryDirectory', start)
    replay = replay[:start] + '        files = ' + repr(ordered + ['Challenge.lean', 'Solution.lean', 'EndpointAudit.lean', 'Identity.lean']) + replay[end:]
    marker = "        result['temporary_compiled_objects_removed'] = True"
    controls = '''            controls = [('ChallengeTrustRejection', 'sorryAx'),
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
'''
    replay = replay.replace(marker, controls + marker)
    write('reproduce.py', replay)
    if args.reviews_root:
        inputs = []
        for reviewer in ['inventory', 'verification']:
            src = args.reviews_root / 'tr26-isotropic-review' / reviewer
            assert (src / 'REVIEW.md').is_file(), src
            dst = out / 'reviews/isotropic' / reviewer
            shutil.copytree(src, dst)
            for p in sorted(dst.rglob('*')):
                if p.is_file():
                    assert p.suffix not in ['.olean', '.ilean'], p
                    data = p.read_bytes()
                    inputs.append({'path': p.relative_to(out).as_posix(),
                                   'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
        js('reviews/SOURCE_REVIEW_BINDINGS.json',
           {'proof_source_ref': SOURCE_REF, 'scope': 'Two independent non-author exact isotropic endpoint source approvals; canonical package review and Linux receipt are separate.',
            'files': inputs})
        m = json.loads((out / 'formalization.yaml').read_text())
        m['project']['authors'] = ['OpenAI Codex AI agents /root, /root/proof_route and /root/ie22_sampling (formalization); /root/inventory and /root/verification (independent exact source review)']
        m['review'] = {'status': 'Exact endpoint independently AI-agent source reviewed; canonical package approval and isolated Linux receipts are retained separately',
                       'reviewers': ['/root/inventory', '/root/verification'],
                       'notes': 'Both reviewers approved immutable source checkpoint 4692336f0e1a50d5e261bba68277875da30fba51. Raw reports, source snapshots, consumers, scripts and fresh-build logs are copied verbatim under reviews/isotropic. No full Target or Linux/Comparator acceptance is implied by source review.'}
        m['status']['main_results'][0]['verification_status'] = 'Actual theorem passes author and two independent fresh LeanCert kernel source audits; isolated Linux/Comparator acceptance is reported separately by a source-bound receipt.'
        js('formalization.yaml', m)
        readme = (out / 'README.md').read_text().replace(
            'Author macOS LeanCert kernel acceptance is established. Independent endpoint/package review and authentic isolated Linux Comparator/raw-kernel receipts are still pending for this package. No such receipt is implied by a local build.',
            'Author and two independent non-author LeanCert kernel source reviews approve the exact endpoint at the immutable source checkpoint above; their full reproducible evidence is retained under reviews/isotropic. Canonical package review and authentic isolated Linux Comparator/raw-kernel receipts are separate gates, reported with their own source-bound receipts. No Linux acceptance is implied by a local source build or source approval.')
        write('README.md', readme)
    files = {}
    for p in sorted(out.rglob('*')):
        if p.is_file():
            data = p.read_bytes()
            files[p.relative_to(out).as_posix()] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
    js('PACKAGE_LOCK.json', {'proof_source_ref': SOURCE_REF,
                             'scope': 'One literal isotropic endpoint only; full Target unproved', 'files': files})
    print(json.dumps({'output': str(out), 'locked_inputs': len(files), 'lean_inputs': len(ordered) + 4,
                      'exact_shared_copies': len(ordered), 'full_target_proved': False}))


if __name__ == '__main__':
    main()
