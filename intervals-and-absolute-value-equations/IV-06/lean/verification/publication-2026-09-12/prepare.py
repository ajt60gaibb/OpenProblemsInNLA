from pathlib import Path
from datetime import datetime, timezone
import collections, hashlib, json, re, subprocess, yaml

repo = Path('/tmp/nla-lean-iv06-worktree')
entry = repo/'intervals-and-absolute-value-equations/IV-06'
project = entry/'lean'
pub = project/'verification/publication-2026-09-12'
candidate = '18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb'
base = '5830ed4fb06da0659414a3deb2a40ad327aca052'
head = '4c075f14209e85ef867eea90eacbea1e05e13a61'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
assert git('rev-parse', 'HEAD').decode().strip() == head
assert not pub.exists()
assert sha(project/'verification/root-operational-2026-09-12/ROOT-CHECKS.json') == 'bfcea16a79ad3398dc902dbb0ab3ca7014d0f70cf7460db1e7731f1c976a6259'
assert sha(project/'verification/linux-2026-09-12/EVIDENCE-MANIFEST.json') == 'b4cde7e528bbf53ba50291e73d48ff27d490df228fbc0e9cea0f9d54011bc7d0'
prefix = project.relative_to(repo).as_posix()+'/'
inputs = {}
for path in git('ls-tree','-r','--name-only',candidate,'--',prefix).decode().splitlines():
    rel = path.removeprefix(prefix)
    h = hashlib.sha256(git('show',candidate+':'+path)).hexdigest()
    assert sha(project/rel) == h, rel
    inputs[rel] = h
assert len(inputs) == 200
evidence = {}
for directory, expected in [('linux-2026-09-12',347),('root-operational-2026-09-12',6)]:
    root = project/'verification'/directory
    outer = root/'EVIDENCE-MANIFEST.json'
    data = json.loads(outer.read_text())
    assert len(data['files']) == expected
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p != outer}
    assert actual == set(data['files'])
    for rel, value in data['files'].items():
        assert sha(root/rel) == value['sha256'] and (root/rel).stat().st_size == value['bytes'], rel
    evidence.update({p.relative_to(project).as_posix():sha(p) for p in root.rglob('*') if p.is_file()})
assert len(evidence) == 355
registry = json.loads((repo/'problem_ids.json').read_text())
canonical = (entry/'README.md').read_text()
target = canonical[canonical.index('## Problem statement'):]
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/path).read_text(),re.M).group(1).strip() for path in registry.values())
assert counts == {'Lean verified':16,'Solved':76,'Open':53,'Partially resolved':72},counts
pub.mkdir(); (pub/'archive').mkdir()
for source,dest in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    (pub/'archive'/dest).write_bytes((project/source).read_bytes())
before = dict(created_utc=datetime.now(timezone.utc).isoformat(),candidate=candidate,upstream=base,integration=head,
    candidate_inputs=inputs,operational_evidence=evidence,canonical_target_tail_sha256=hashlib.sha256(target.encode()).hexdigest(),
    other_canonical={i:sha(repo/p) for i,p in registry.items() if i!='IV-06'},
    problem_ids_sha256=sha(repo/'problem_ids.json'),counts_before=dict(counts),
    resolved_before_sha256=sha(repo/'RESOLVED.md'))
(pub/'before.json').write_text(json.dumps(before,indent=2)+'\n')
(pub/'integration.json').write_bytes(Path('/tmp/nla-lean-formalization/IV-06-upstream-integration.json').read_bytes())

section = r'''## Lean proof and verification evidence - 2026-09-12

**The complete original component-bound conjecture is Lean verified with a negative answer.** The [proof at revision 18b5ef3](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean) proves that the unchanged dimension-three source box has at least four actual connected components. It retains the full independent-entry interval family, genuine nonzero real eigenvectors and the topology of the attained real-eigenvalue subset. Component cardinality is the actual `Cardinal` of `ConnectedComponents`; no finiteness, symmetry or all-real-spectrum assumption is added.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains authorship of the mathematical counterexample. Milan Hladík, David Daney and Elias P. Tsigaridas retain the original question and background credit.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean/Solution.lean), each with prefix `NLA.IV06.`, are:

- `eigenvalue_determinant_semantics`: genuine eigenvector and characteristic-determinant equivalence for every real square matrix.
- `family_and_determinant_semantics`: equality with the complete endpoint box and the actual determinant polynomial.
- `witness_eigenpairs`: four admissible matrices and their nonzero eigenvectors at $`-3,0,3,25`$.
- `witness_separators`: determinant bounds for every box member, excluding $`-1,1,12`$.
- `connected_component_intervals`: actual equal component classes force interval containment for any real subset.
- `four_components`: an injective map from four representatives into the genuine component quotient.
- `counterexample`: admissible endpoints whose component cardinality strictly exceeds dimension three.
- `not_componentBoundConjecture`: negation of the complete original universal claim.

Two independent statement approvals preceded implementation; two independent final proof referees approved the frozen proof after fresh source elaboration and actual-term checks. [Ubuntu run 34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519) matched all eight exports with the sandboxed Comparator, replayed the solution in Lean's default kernel and passed both actual isolation/rejection-control suites. The [operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind all 200 candidate inputs; the [separate root acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) independently checked their identity and actual execution. All 17 internal/public transitive axiom reports allow only `propext`, `Classical.choice` and `Quot.sound`. Operational and publication work does not add mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). A material explicit kernel LeanCert certificate proves $`-18<0`$ on a singleton; exact algebra and universal affine bounds reduce every separator to this sign. Genuine connectedness and cardinality complete the argument. No eigenvalue approximation, root isolation or interval subdivision is used. Exactly four components, complete endpoints and a replacement bound for all dimensions are outside these exports. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml), [reviews](lean/reviews/) and [dependency pins](lean/lake-manifest.json).

From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  intervals-and-absolute-value-equations/IV-06/lean \
  /absolute/path/to/nla-lean-tools
```

'''
assert canonical.count('**Status:** Solved') == 1
canonical = canonical.replace('**Status:** Solved','**Status:** Lean verified',1).replace('**Last checked:** 2026-09-11','**Last checked:** 2026-09-12',1)
old = 'This is agent verification, not external human peer review or formal proof-assistant certification.'
assert old in canonical
canonical = canonical.replace(old,'That original agent review was informal; the later Lean verification is documented below. External human peer review is not claimed.',1)
canonical = canonical.replace('## Problem statement',section+'## Problem statement',1)
assert canonical[canonical.index('## Problem statement'):] == target
(entry/'README.md').write_text(canonical)

readme = (project/'README.md').read_text()
readme = readme.replace('# IV-06: complete Lean proof, Linux verification pending','# IV-06: verified interval-eigenvalue component counterexample',1)
old = readme.split('\n\n')[1]
assert old.startswith('**The complete original interval-eigenvalue')
readme = readme.replace(old,'**The complete original interval-eigenvalue component conjecture is Lean verified with a negative answer and all eight reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals followed. The unchanged proof at [revision 18b5ef3](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/'+candidate+'/intervals-and-absolute-value-equations/IV-06/lean) passed actual sandboxed Linux Comparator/default-kernel verification in [run 34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519). The [independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](verification/root-operational-2026-09-12/ROOT-CHECKS.json) checked the real execution and all 200 submitted inputs. The [canonical entry](../README.md) records the complete verified scope.',1)
readme = readme.replace('The implementation and this packaging are by the same agent, `/root/solved_statement_inventory`; packaging is not an additional independent mathematical review.','The implementation and historical candidate packaging are by `/root/solved_statement_inventory`. Publication preparation is by `/root`, who also served as statement referee 1 and final proof referee 2; packaging and operational acceptance are not additional mathematical reviews.',1)
readme = readme.replace('records the exact scope, attribution, reviews and pending Linux gate.','records the exact scope, attribution, reviews and completed Linux gate.',1)
readme = readme.replace('Once the candidate has an immutable Git revision, use the [shared workflow]','From the immutable verified revision, use the [shared workflow]',1)
marker = 'Actual project-specific Linux Comparator/default-kernel execution and controls, independent operational review, and publication review remain required before promotion.'
assert marker in readme
readme = readme[:readme.index(marker)]+'''## Actual Linux verification and publication preservation

The successful Ubuntu 24.04 run freshly cloned all ten dependencies at their exact pins and used 8690 official Mathlib cache artifacts before checking the project source. Challenge and Solution build graphs completed with 1916 and 2918 jobs respectively; these graph counts do not assert full dependency-source rebuilds. The solution emitted no warnings. Its eight declarations matched without definition exceptions, default-kernel replay passed, and all seventeen internal/public transitive axiom reports contained exactly the standard three.

The target job and separate checker job each passed the actual sandbox probes, three raw-kernel controls, five Comparator fixtures and the admission/native-execution negative controls. The nested Bubblewrap executable was denied UID-map creation before its inner write; this does not claim that the write executed or establish general sandbox security. Complete raw logs and original artifact ZIPs are preserved. The [Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) binds 347 files plus itself, including every nested manifest. Original project ZIP SHA-256 is `bbe96d9e07020993524329a33ea366ff0ab85707d666b0974bd06c667af0e005`; checker-control ZIP SHA-256 is `3c405009704da285d05939461fec1bb38f8a8fe4f9e7f52339f2da4f689c0529`. Both match GitHub metadata and upload logs. The separately retained 152-file run-log ZIP has a locally computed digest; no GitHub-published log-archive digest is claimed.

Operational reviewer `/root/formal_review_standards`, also statement referee 2 and a shared-harness contributor, did not implement this proof. The root coordinator independently accepted the audit and actual GitHub records; root also served as final mathematical referee 2. These roles do not increase the number of independent mathematical reviewers. The [root operational evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json) retains its six checked files plus itself.

The successful run verifies the immutable candidate, not a later metadata revision. Publication changes only this README and five status/review fields in the current manifest among its 200 submitted inputs. All other 198 inputs, all 348 Linux evidence files and all seven root operational evidence files remain byte-identical. The exact preceding [README](verification/publication-2026-09-12/archive/README.linux-candidate.md) and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml) are archived. All 125 non-README proof-freeze inputs and the historical README archive are preserved, as are all eight original source snapshots. The canonical original problem statement and mathematical source are unchanged. Earlier phase-specific pending notices remain historical records. Publication does not rerun the proof or claim external human review, official Tau Ceti endorsement, source-author endorsement or new mathematical priority.
'''
(project/'README.md').write_text(readme)

path = project/'formalization.yaml'
header = path.read_text().splitlines()[0]
manifest = yaml.safe_load(path.read_text())
manifest['status']['scope'] = 'Complete negative answer to the full original universal interval-eigenvalue component-bound conjecture. All eight exports retain the full independent-entry box, genuine nonzero real eigenvectors and actual Cardinal of ConnectedComponents. The unchanged dimension-three source box has at least four components, without a finite-component premise. Two independent statement and two independent final proof approvals were followed by actual Ubuntu sandboxed Comparator/default-kernel success in run 34725713519 at '+candidate+'. Independent operational review and root acceptance bind all 200 inputs, actual execution and both real control suites. Canonical status is Lean verified.'
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = 'Both independent statement approvals preceded implementation. Both final referees freshly elaborated the proof in separate private prefixes, inspected actual terms, independently reconstructed exact universal bounds and repeated the retained LeanCert Boolean checker with decide +kernel. Seventeen internal/public assertions and transitive axiom reports allow only propext, Classical.choice and Quot.sound. The material interval certificate is exactly -18<0 in explicit kernel mode on a singleton, consumed through separator exclusion to the full negation. Local checks ran on macOS with read-only matching pinned MI-22 dependency objects and no old IV-06 project objects. Actual Ubuntu run 34725713519 at '+candidate+' freshly cloned ten exact dependencies, used 8690 official Mathlib cache artifacts, built the sources, matched all eight exports without definition exceptions, replayed the default kernel and passed both actual control suites. No full dependency-source rebuild is claimed. The nested Bubblewrap executable was denied UID-map creation before its inner write. Independent operational reviewer /root/formal_review_standards also served as statement referee 2 and contributed to shared infrastructure; proof author is /root/solved_statement_inventory. Root independently accepted actual execution and retained identity; root also served as final proof referee 2 and prepared publication metadata. These additional roles do not add mathematical referees. Operational report SHA256 4e212afc2458805a3684748939e46f47dac3e1f6e7576bb5fc8dc591d75ed7c8 and outer evidence b4cde7e528bbf53ba50291e73d48ff27d490df228fbc0e9cea0f9d54011bc7d0 bind 347 files plus the outer manifest, retaining every nested manifest. Root checks SHA256 bfcea16a79ad3398dc902dbb0ab3ca7014d0f70cf7460db1e7731f1c976a6259 independently confirm the acceptance. Publication archives both prior wrappers, changes only this manifest and README among 200 candidate inputs, and preserves all 198 others, 348 Linux files and seven root operational files. All 125 non-README proof-freeze inputs, the archived statement README and eight original source snapshots remain intact. Earlier phase notices are historical. No new proof run over publication wrappers, external human review, official Tau Ceti endorsement or priority is claimed.'
manifest['review']['linux_verification']['status'] = 'passed; independently audited and root accepted'
manifest['review']['linux_verification']['note'] = 'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519 at '+candidate+'. Eight matched exports, seventeen standard-three axiom reports, actual default-kernel replay and both full control suites passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md, its EVIDENCE-MANIFEST.json and verification/root-operational-2026-09-12/ROOT-CHECKS.json. Original project ZIP SHA256 bbe96d9e07020993524329a33ea366ff0ab85707d666b0974bd06c667af0e005; checker-control ZIP SHA256 3c405009704da285d05939461fec1bb38f8a8fe4f9e7f52339f2da4f689c0529. Complete raw run-log archive is retained with its separately computed digest.'
path.write_text(header+'\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))

resolved = (repo/'RESOLVED.md').read_text()
start = resolved.index('### IV-06 - Negative resolution')
end = resolved.index('\n## ',start+1)
block = resolved[start:end]
block = block.replace('### IV-06 - Negative resolution','### IV-06 - Negative resolution by Matthew J. Colbrook; Lean formalization by George Stepaniants',1)
block = block.rstrip()+r'''

**Lean verified - 2026-09-12.** The [eight checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean/Solution.lean) negate the complete original universal component bound using the unchanged dimension-three box with at least four actual components. Full independent-entry variation, genuine nonzero eigenvectors, real subset topology and `Cardinal` component counts are retained; no finiteness premise is assumed. **Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance. Matthew J. Colbrook retains mathematical counterexample credit; Hladík, Daney and Tsigaridas retain original-question credit. See the [canonical verification evidence](intervals-and-absolute-value-equations/IV-06/README.md#lean-proof-and-verification-evidence---2026-09-12), [statement and final proof reviews](intervals-and-absolute-value-equations/IV-06/lean/reviews/), [successful Ubuntu run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519), [operational audit](intervals-and-absolute-value-equations/IV-06/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](intervals-and-absolute-value-equations/IV-06/lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json). All 200 inputs, seventeen standard-three axiom reports, actual default-kernel replay and both real control suites were checked. The material explicit kernel LeanCert computation is the singleton sign $`-18<0`$; exact algebra and topology complete the argument. Additional operational and publication roles do not add mathematical referees. Exactly four components, every endpoint and an all-dimension replacement bound are outside these exports. External human peer review is not claimed.

'''
(repo/'RESOLVED.md').write_text(resolved[:start]+block+resolved[end:])
(pub/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(prepared=True,candidate=candidate,integrated_head=head,inputs=len(inputs),retained_operational_files=len(evidence)),indent=2))
