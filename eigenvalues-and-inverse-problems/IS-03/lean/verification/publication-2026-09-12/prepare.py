from pathlib import Path
from datetime import datetime, timezone
import collections, hashlib, json, re, subprocess, yaml

repo = Path('/tmp/nla-lean-is03-worktree')
entry = repo/'eigenvalues-and-inverse-problems/IS-03'
project = entry/'lean'
pub = project/'verification/publication-2026-09-12'
candidate = 'f87375fa5d7926fe0e065199eaab8f15ac5a5e48'
base = '5830ed4fb06da0659414a3deb2a40ad327aca052'
head = 'ab164900f806ab7208ca8b0107a6238603eaacad'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
assert git('rev-parse', 'HEAD').decode().strip() == head
assert not pub.exists()
assert sha(project/'verification/root-operational-2026-09-12/ROOT-CHECKS.json') == 'f1a0d3936711ed76c006d7f59c62dd227f3a52812567578fafa284d8aa7bf154'
assert sha(project/'verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json') == '6177b018d1cdd68dd70222dc3dc6f9cf6cca7030707c07bbb8af2b21b36e4674'
assert sha(project/'verification/linux-2026-09-12/EVIDENCE-MANIFEST.json') == '66d3eef4f5a6b67f9d9aec94187af141cdda626b8c6d88b9b5c8e8e82c8ccd14'
assert sha(project/'verification/linux-2026-09-12/OPERATIONAL-REVIEW.md') == '97d43157105cc4abe654c5cd222a2e7928028d2f687f04ee3435ef6c589aff1f'
prefix = project.relative_to(repo).as_posix()+'/'
inputs = {}
for path in git('ls-tree','-r','--name-only',candidate,'--',prefix).decode().splitlines():
    rel = path.removeprefix(prefix)
    h = hashlib.sha256(git('show',candidate+':'+path)).hexdigest()
    assert sha(project/rel) == h, rel
    inputs[rel] = h
assert len(inputs) == 303
assert git('show','-s','--format=%ae%x00%ce',head).rstrip(b'\n') == b'\0'
evidence = {}
for directory, expected in [('linux-2026-09-12',444),('root-operational-2026-09-12',6)]:
    root = project/'verification'/directory
    outer = root/'EVIDENCE-MANIFEST.json'
    data = json.loads(outer.read_text())
    assert len(data['files']) == expected
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p != outer}
    assert actual == set(data['files'])
    for rel, value in data['files'].items():
        f=root/rel
        assert f.resolve().is_relative_to(root.resolve()) and not f.is_symlink()
        assert sha(f) == value['sha256'] and f.stat().st_size == value['bytes'], rel
    evidence.update({p.relative_to(project).as_posix():sha(p) for p in root.rglob('*') if p.is_file()})
assert len(evidence) == 452
receipt=json.loads(Path('/tmp/nla-lean-formalization/IS-03-upstream-integration.json').read_text())
assert receipt['candidate_inputs']==inputs and receipt['integration_commit']==head
registry = json.loads((repo/'problem_ids.json').read_text())
canonical = (entry/'README.md').read_text()
target = canonical[canonical.index('## Problem statement'):]
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/path).read_text(),re.M).group(1).strip() for path in registry.values())
assert counts == {'Lean verified':16,'Solved':76,'Open':53,'Partially resolved':72},counts
assert not git('diff','--name-only','HEAD')
pub.mkdir(); (pub/'archive').mkdir()
for source,dest in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    (pub/'archive'/dest).write_bytes((project/source).read_bytes())
before = dict(created_utc=datetime.now(timezone.utc).isoformat(),candidate=candidate,upstream=base,integration=head,
    candidate_inputs=inputs,operational_evidence=evidence,canonical_target_tail_sha256=hashlib.sha256(target.encode()).hexdigest(),
    other_canonical={i:sha(repo/p) for i,p in registry.items() if i!='IS-03'},
    problem_ids_sha256=sha(repo/'problem_ids.json'),counts_before=dict(counts),
    resolved_before_sha256=sha(repo/'RESOLVED.md'))
(pub/'before.json').write_text(json.dumps(before,indent=2)+'\n')
(pub/'integration.json').write_bytes(Path('/tmp/nla-lean-formalization/IS-03-upstream-integration.json').read_bytes())

section = r'''## Lean proof and verification evidence - 2026-09-12

**The complete original derivative-realizability conjecture is Lean verified with a negative answer.** The [proof at revision f87375f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean) proves that the unchanged nonnegative order-seven source matrix has no entrywise-nonnegative realization of its normalized characteristic-polynomial derivative at order six. The full original quantifiers and exact order $`n-1`$ are retained. Neither symmetry nor diagonalizability is assumed; entrywise nonnegativity is not replaced by positive semidefiniteness.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains mathematical counterexample authorship. Johnson and Hoover, McCormick, Paparella and Thrall retain the original conjecture and source attribution.

The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean/Solution.lean), each with prefix `NLA.IS03.`, are:

- `nonnegative_power_trace`: every natural power of an entrywise-nonnegative real matrix has nonnegative entries and trace, including order and power zero.
- `witness_admissible`: the actual source matrix is entrywise nonnegative and has trace $`1/2`$.
- `witness_polynomials`: its genuine characteristic polynomial and normalized derivative have the stated coefficients; the derivative is monic of degree six.
- `trace_moment_certificate`: every real order-six matrix with that characteristic polynomial has all seven prescribed power traces, without a spectral assumption.
- `negative_moment`: the seventh value is exactly $`-8593/823543`$ and strictly negative.
- `counterexample`: the admissible source matrix has no nonnegative order-six realization of its actual normalized derivative.
- `not_derivativeRealizabilityConjecture`: negation of the complete original universal assertion.

Two independent statement approvals preceded implementation; two independent final proof referees approved the frozen proof after fresh source elaboration, actual-term inspection and replay of the retained numerical checker. [Ubuntu run 34728101436](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436) matched all seven exports with the sandboxed Comparator, replayed the solution in Lean's default kernel and passed both actual isolation/rejection-control suites. The [operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind all 303 submitted inputs; [root acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) independently checked their identity and actual execution. All 18 internal/public transitive axiom reports allow only `propext`, `Classical.choice` and `Quot.sound`. Operational and publication roles do not add mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The material explicit kernel LeanCert certificate proves the singleton sign $`-8593/823543<0`$. Exact characteristic-polynomial, spectral, Vieta/Newton and trace arguments connect that sign to the full contradiction. Separability and an actual eigenbasis of any potential realization are derived, not assumed. No approximate roots, numerical eigensolver or interval subdivision is used. The source's stronger zero-padding exclusion and its separate Monov consequence are outside these seven exports. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml), [reviews](lean/reviews/) and [pins](lean/lake-manifest.json).

From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  eigenvalues-and-inverse-problems/IS-03/lean \
  /absolute/path/to/nla-lean-tools
```

'''
assert canonical.count('**Status:** Solved') == 1
canonical = canonical.replace('**Status:** Solved','**Status:** Lean verified',1).replace('**Last checked:** 2026-09-11','**Last checked:** 2026-09-12',1)
old = 'Original ChatGPT generation is disclosed; no external human peer review or formal proof certificate is asserted.'
assert old in canonical
canonical = canonical.replace(old,'Original ChatGPT generation is disclosed; that dated agent review was informal. The later Lean verification is documented below; external human peer review is not claimed.',1)
canonical = canonical.replace('## Problem statement',section+'## Problem statement',1)
canonical = canonical.replace('**Status:** Lean verified  \n**Last checked:** 2026-09-12  \n', '**Status:** Lean verified\n\n**Last checked:** 2026-09-12\n', 1)
assert canonical[canonical.index('## Problem statement'):] == target
(entry/'README.md').write_text(canonical)

readme = (project/'README.md').read_text()
readme = readme.replace('# IS-03: reviewed derivative-realizability counterexample','# IS-03: verified derivative-realizability counterexample',1)
old = readme.split('\n\n')[1]
assert old.startswith('**The complete original conjecture has a locally checked negative proof')
readme = readme.replace(old,'**The complete original derivative-realizability conjecture is Lean verified with a negative answer and all seven reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals followed. The unchanged proof at [revision f87375f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/'+candidate+'/eigenvalues-and-inverse-problems/IS-03/lean) passed actual sandboxed Linux Comparator/default-kernel verification in [run 34728101436](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436). The [independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](verification/root-operational-2026-09-12/ROOT-CHECKS.json) checked the real execution and all 303 submitted inputs. The [canonical entry](../README.md) records the complete verified scope.',1)
old='This documentation was prepared by the latter implementation\nagent.'
assert old in readme
readme=readme.replace(old,'Historical candidate documentation was prepared by the latter implementation\nagent. Publication preparation is by `/root/formal_review_standards`, the\nindependent final mathematical referee 2; this preparation is not an additional\nmathematical review.',1)
readme=readme.replace('For the pending project-specific verification, follow the','From the immutable verified revision, follow the',1)
old='These commands describe the remaining reproducible gate; this package does\nnot claim they have run for IS-03. A successful run on another problem or the\nshared infrastructure does not verify this candidate.'
assert old in readme
readme=readme.replace(old,'These commands reproduce the verification from the immutable candidate. The\nobserved project-specific run and its scope are recorded below; success on\nunrelated projects is not used to verify IS-03.',1)
readme=readme.replace('records the complete scope and pending\nLinux gate.','records the complete scope and completed\nLinux gate.',1)
old='The next steps are coordinator candidate review, an immutable candidate\ncommit, actual Linux verification with controls, independent operational\nreview and publication review. Canonical status promotion and an individual\nupstream PR follow those gates.'
assert old in readme
readme=readme.replace(old,'''## Actual Linux verification and publication preservation

The successful Ubuntu 24.04 run freshly cloned all ten dependencies at their
exact pins and used 8690 official Mathlib cache artifacts before checking the
project source. Challenge and Solution build graphs completed with 1718 and
3101 jobs respectively; these graph counts do not assert full dependency-source
rebuilds. The Solution phase emitted no warnings. Its seven declarations matched
without definition exceptions, default-kernel replay passed, and all eighteen
internal/public transitive axiom reports contained exactly the standard three.

The target job and separate checker job each passed the actual sandbox probes,
three raw-kernel controls, five Comparator fixtures and the admission/native
execution negative controls. The nested Bubblewrap executable was denied
UID-map creation before its inner write; this does not claim that the inner
write executed or establish general sandbox security. Complete raw logs and
original artifact ZIPs are retained. The [Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json)
binds 444 files plus itself, including every nested manifest. Original project
ZIP SHA-256 is `5a72c6ed55af7aea388b74910cd0b0cbc2c81004427b145390fbe74f4ec1ac1e`;
checker-control ZIP SHA-256 is
`2ef6c60b6f7e7367fd72ba3e484ab7e350cf8970c8e6ae880bb4bbff494c5cb5`.
Both match GitHub metadata and actual upload logs. The retained 152-file full
run-log ZIP has a separately computed digest; no GitHub-published checksum
for that archive is claimed.

Operational reviewer `/root/leancert_examples` also served as independent
statement and final mathematical referee 1 and authored neither the statements
nor the proof. The root coordinator independently accepted the operational
evidence and actual GitHub records; root and `/root/solved_statement_inventory`
coauthored the proof and do not count as independent final referees. Publication
preparer `/root/formal_review_standards` is the other independent statement/final
referee and also contributed shared infrastructure. These roles do not increase
the number of mathematical referees. The [root operational evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json)
retains six checked files plus itself.

The successful run verifies the immutable candidate, not a later metadata
revision. Publication changes only this README and five status/review fields
in the current manifest among its 303 submitted inputs. All other 301 inputs,
all 445 Linux evidence files and all seven root operational evidence files
remain byte-identical. The exact preceding [README](verification/publication-2026-09-12/archive/README.linux-candidate.md)
and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml)
are archived. All 202 non-README proof-freeze inputs, all 34 statement inputs
through their exact README archive, all ten original source snapshots and every
review/evidence record are preserved. The canonical original problem statement
and mathematical source are unchanged. Earlier phase-specific pending notices
remain historical records.

A separate publication review remains required before a publication commit,
push and individual upstream PR. This preparation reruns no Lean proof and
claims no external human review, official Tau Ceti endorsement, source-author
endorsement or new mathematical priority.''',1)
(project/'README.md').write_text(readme)

path = project/'formalization.yaml'
header = path.read_text().splitlines()[0]
manifest = yaml.safe_load(path.read_text())
manifest['status']['scope'] = 'Complete negative answer to the full original universal derivative-realizability conjecture. All seven exports retain every n at least five, entrywise-nonnegative real matrices and a realization of exactly order n-1. The unchanged nonnegative order-seven source matrix has no order-six realization of its actual normalized characteristic-polynomial derivative. No symmetry or diagonalizability is assumed. Two independent statement and two independent final proof approvals were followed by actual Ubuntu sandboxed Comparator/default-kernel success in run 34728101436 at '+candidate+'. Independent operational review and root acceptance bind all 303 inputs, actual execution and both real control suites. Canonical status is Lean verified.'
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = 'Both independent statement approvals preceded implementation. Both final referees freshly elaborated the proof in separate private prefixes, inspected actual terms and semantic dependencies, independently reconstructed exact characteristic polynomials, Bezout and trace identities, and replayed the material LeanCert Boolean checker with decide +kernel. Eighteen internal/public kernel assertions and transitive axiom reports allow only propext, Classical.choice and Quot.sound. The material certificate is exactly -8593/823543<0 in explicit kernel mode on a singleton, consumed through the negative seventh trace to the full original negation. Actual spectral, Vieta/Newton and trace arguments derive an eigenbasis for any potential realization rather than assuming diagonalizability. Local proof checks ran on macOS with read-only pinned MI-22 dependency objects and no old IS-03 project objects. Actual Ubuntu run 34728101436 at '+candidate+' freshly cloned ten exact dependencies, used 8690 official Mathlib cache artifacts, built the source, matched all seven exports without definition exceptions, replayed the default kernel and passed both actual control suites. Graph counts were 1718 for Challenge and 3101 for Solution; no full dependency-source rebuild is claimed. Nested Bubblewrap was denied UID-map creation before its inner write. Independent operational reviewer /root/leancert_examples also served as independent statement and final referee 1. Root and /root/solved_statement_inventory coauthored the statements/proof; root operational acceptance is not an independent mathematical review. Publication preparer /root/formal_review_standards is independent final referee 2 and a shared-infrastructure contributor; preparation adds no mathematical referee. Operational report SHA256 97d43157105cc4abe654c5cd222a2e7928028d2f687f04ee3435ef6c589aff1f and outer evidence 66d3eef4f5a6b67f9d9aec94187af141cdda626b8c6d88b9b5c8e8e82c8ccd14 bind 444 files plus the outer manifest, retaining every nested manifest. Root checks SHA256 f1a0d3936711ed76c006d7f59c62dd227f3a52812567578fafa284d8aa7bf154 separately confirm acceptance. Publication archives both prior wrappers, changes only README and this manifest among 303 candidate inputs, and preserves all 301 others, all 445 Linux files and seven root operational files. All 202 non-README proof-freeze inputs, the exact historical README archive, 34 statement inputs and ten original source snapshots remain intact. Earlier phase notices are historical. No new proof run over publication wrappers, external human review, official Tau Ceti endorsement or priority is claimed.'
manifest['review']['linux_verification']['status'] = 'passed; independently audited and root accepted'
manifest['review']['linux_verification']['note'] = 'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436 at '+candidate+'. Seven matched exports, eighteen standard-three axiom reports, actual default-kernel replay and both full control suites passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md, its EVIDENCE-MANIFEST.json and verification/root-operational-2026-09-12/ROOT-CHECKS.json. Original project ZIP SHA256 5a72c6ed55af7aea388b74910cd0b0cbc2c81004427b145390fbe74f4ec1ac1e; checker-control ZIP SHA256 2ef6c60b6f7e7367fd72ba3e484ab7e350cf8970c8e6ae880bb4bbff494c5cb5. Complete original run-log archive is retained with its separately computed digest.'
path.write_text(header+'\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))

resolved = (repo/'RESOLVED.md').read_text()
start = resolved.index('#### IS-03 — negative resolution')
# End at the NEXT heading of equal or higher level, not the end of the shared group.
next_heads=[m.start() for m in re.finditer(r'(?m)^#{1,4} ',resolved) if m.start()>start]
assert next_heads
end=min(next_heads)
block = resolved[start:end]
block = block.replace('#### IS-03 — negative resolution','#### IS-03 — negative resolution by Matthew J. Colbrook; Lean formalization by George Stepaniants',1)
block = block.rstrip()+r'''

**Lean verified - 2026-09-12.** The [seven checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean/Solution.lean) negate the complete original derivative-realizability conjecture using the unchanged nonnegative order-seven source matrix and the impossibility of an exact-order-six realization. Actual characteristic-polynomial differentiation, arbitrary-real-matrix power traces and all original quantifiers are retained, without symmetry or diagonalizability assumptions. **Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance. Matthew J. Colbrook retains mathematical counterexample credit; Johnson and Hoover, McCormick, Paparella and Thrall retain original-question credit. See the [canonical verification evidence](eigenvalues-and-inverse-problems/IS-03/README.md#lean-proof-and-verification-evidence---2026-09-12), [statement and final reviews](eigenvalues-and-inverse-problems/IS-03/lean/reviews/), [successful Ubuntu run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436), [operational audit](eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](eigenvalues-and-inverse-problems/IS-03/lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json). All 303 inputs, eighteen standard-three axiom reports, actual default-kernel replay and both real control suites were checked. The material explicit kernel LeanCert computation is the singleton sign $`-8593/823543<0`$; exact algebra, derived spectral semantics and Newton identities complete the argument. Operational and publication work does not add mathematical referees. The stronger zero-padding exclusion and separate Monov consequence remain informal source results outside these seven exports. External human peer review is not claimed.

'''
(repo/'RESOLVED.md').write_text(resolved[:start]+block+resolved[end:])
(pub/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(prepared=True,candidate=candidate,integrated_head=head,inputs=len(inputs),retained_operational_files=len(evidence)),indent=2))
