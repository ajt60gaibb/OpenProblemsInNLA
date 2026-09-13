from pathlib import Path
from datetime import datetime, timezone
import collections, hashlib, json, re, subprocess, yaml
repo=Path('/tmp/nla-lean-fr12-worktree'); entry=repo/'frames-and-matrix-designs/FR-12'; project=entry/'lean'; work=Path('/tmp/nla-lean-formalization/fr12-publication'); pub=project/'verification/publication-2026-09-12'
revision='3e20bae9a07b1a33db8fdfb18bdebb9e590071a9'; base='f41f1f9ffa2171550d4bb795862c6170c4f26070'; run=34718277411
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
pre=json.loads((work/'before-integration.json').read_text()); integration=json.loads((work/'integration.json').read_text())
assert git('rev-parse','HEAD').decode().strip()==integration['integration_commit']
for group in ['verified_inputs','operational_files']:
 for name,h in pre[group].items():assert sha(project/name)==h,name
assert not pub.exists(); pub.mkdir()
canonical=(entry/'README.md').read_text();target=canonical[canonical.index('## Statement'):]
registry=json.loads((repo/'problem_ids.json').read_text())
counts=collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)',(repo/p).read_text(),re.M).group(1).strip() for p in registry.values())
before={'created_utc':datetime.now(timezone.utc).isoformat(),'verified_revision':revision,'verified_run':run,'base':base,'integrated_head':integration['integration_commit'],'all_verified_inputs':pre['verified_inputs'],'all_operational_evidence':pre['operational_files'],'canonical_target_tail_sha256':hashlib.sha256(target.encode()).hexdigest(),'other_canonical':{i:sha(repo/p) for i,p in registry.items() if i!='FR-12'},'problem_ids_sha256':sha(repo/'problem_ids.json'),'branch_counts_before':dict(counts)}
(pub/'before.json').write_text(json.dumps(before,indent=2)+'\n')
for name in ['integration.json','integration.log','snapshot.py','before-integration.json']:(pub/name).write_bytes((work/name).read_bytes())
section=r'''## Lean proof and verification evidence - 2026-09-12

**The complete original counting conjecture has a Lean-verified negative answer.** The [proof at revision 3e20bae](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean) counts actual labeled real Hadamard matrices, proves the count finite, and refutes every proposed positive real constant. **Mathematical proof and Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI-agent assistance.

The formal construction uses top-to-bottom pairings indexed by a permutation and proves

```math
m!\,H(m)^2\le H(2m)\qquad(m\ge1).
```

This smaller family yields the identical quantitative power-of-two lower bound above and the full original negation. **The stronger informal factor $`(2m-1)!!`$ is outside the Lean exports.** The formal count has no quotient, normalization or assumed family size; in positive dimension its matrix predicate is proved equivalent to Mathlib's `Matrix.IsHadamard`.

The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean/Solution.lean), each with prefix `NLA.FR12.`, are:

- `counting_semantics`: genuine finite counting and the Mathlib Hadamard bridge.
- `injective_doubling`: every constructed output is Hadamard and the map is injective.
- `factorial_doubling`: the cardinality recurrence for every positive order.
- `power_two_nonempty`: existence at every power of two, including order one.
- `power_two_lower_bound`: the exact source lower bound at every $`K\ge2`$.
- `counterexample`: a strict violation for every positive real proposed constant.
- `not_countingConjecture`: negation of the complete original universal assertion.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34718277411](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411) matched all seven exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) bind all 137 input files and both actual isolation/rejection-control suites. All 14 [internal/public transitive axiom checks](lean/verification/linux-2026-09-12/axiom-verification.json) use only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews; external human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits the exact proof's kernel trust; there is **no numerical interval certificate**. Symbolic injection and direct exponential induction avoid large enumerations or approximate logarithms. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  frames-and-matrix-designs/FR-12/lean \
  /absolute/path/to/nla-lean-tools
```

'''
assert canonical.count('**Status:** Solved')==1
canonical=canonical.replace('**Status:** Solved  \n','**Status:** Lean verified\n',1)
old='Substantial AI assistance is disclosed; this is informal automated review, not external human peer review or formal verification.'
assert old in canonical
canonical=canonical.replace(old,'Substantial AI assistance is disclosed. That review was informal and did not assert external human peer review or formal verification; the later Lean verification is documented below.',1)
canonical=canonical.replace('## Statement',section+'## Statement',1)
assert canonical[canonical.index('## Statement'):]==target
(entry/'README.md').write_text(canonical)

readme=(project/'README.md').read_text();start=readme.index('The complete original');end=readme.index('\n**Mathematical proof',start)
readme=readme[:start]+'''The complete original labeled real Hadamard counting conjecture has a
**Lean-verified negative answer** as of 12 September 2026. The unchanged proof at
[revision 3e20bae](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean)
passed two independent statement reviews before implementation, two independent
final proof reviews, and actual Linux sandboxed Comparator/default-kernel
verification in [run 34718277411](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411).
The [independent operational audit and original artifacts](verification/linux-2026-09-12/)
bind all seven exports and the complete 137-file verified input set. The
[canonical entry](../README.md) records the complete verified scope and status.
''' + readme[end:]
old='''The author's 2157-job build and the independent fresh-source checks are local
macOS runs with matching compiled dependency reuse at ten clean pinned Git
revisions. They do not claim all Mathlib dependencies were rebuilt from source
or that the Linux verifier ran. The relevant
[pinned Tau Ceti standards](../../../docs/lean/REVIEW.md) were applied within
the scope of this complete original target.'''
new='''The author's 2157-job build and the independent fresh-source reviews were
local macOS runs with matching compiled dependency reuse at ten clean pinned
Git revisions. The later Linux job freshly cloned all ten dependencies at
their exact revisions and used 8690 official Mathlib cache artifacts before
building the project source. Neither phase claims to rebuild every dependency
from source. Both the project job and separate checker job passed actual
isolation and rejection controls. The nested Bubblewrap executable was denied
UID-map creation before its inner write; that probe is not a general sandbox
security guarantee. The relevant [pinned Tau Ceti standards](../../../docs/lean/REVIEW.md)
were applied within the scope of this complete original target.'''
assert old in readme;readme=readme.replace(old,new,1)
readme=readme.replace('## Reproduction and pending Linux gate','## Reproduction and verified Linux gate',1)
old='''After the candidate has an immutable Git revision, use the repository's
[shared workflow](../../../docs/lean/README.md) on a correctly configured
[non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:'''
new='''From the immutable verified revision, use the repository's
[shared workflow](../../../docs/lean/README.md) on a correctly configured
[non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:'''
assert old in readme;readme=readme.replace(old,new,1)
start=readme.index('The actual run must build/export')
readme=readme[:start]+'''The actual successful run built and exported the independently checked
Challenge and Solution, compared all seven declarations with no definition
exceptions, replayed the proof through Lean's default kernel, and passed the
real isolation and rejection controls. [Comparator](comparator.json) permits
only the three standard axioms. The [complete Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json)
retains both original artifact ZIPs, complete raw logs, every submitted input
hash, checked tool sources and the independent operational report. It binds
255 files plus itself, including every nested manifest.

The exact historical README remains archived at
[the frozen statement-stage copy](verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md).
At candidate packaging, only this README changed among the 74 proof-freeze
inputs. Publication changes only this README and the current formalization
manifest among the 137 Linux-verified input files. All other 135 mathematical
sources, statements, configurations, pins and prior review/evidence inputs
remain identical, as do all 256 retained operational evidence files. Original
phase labels and metadata snapshots remain intact. The successful run is bound
to the immutable proof revision; no new run over these publication wrappers
is claimed. The original canonical target and informal manuscript are unchanged.
'''
(project/'README.md').write_text(readme)

mp=project/'formalization.yaml';header=mp.read_text().splitlines()[0];manifest=yaml.safe_load(mp.read_text())
manifest['sources'][0]['note']='Retains the individual labeled sign-matrix count, arbitrary positive real C, every positive natural dimension divisible by four and the genuine base-two logarithm. The original source is informally Solved. Its complete target now has actual independently audited Linux Lean verification at revision '+revision+'.'
manifest['status']['scope']='Complete negative answer to the original canonical labeled real Hadamard counting conjecture. All seven exports passed two independent statement reviews, two independent final proof reviews and actual Linux sandboxed Comparator/default-kernel verification in run 34718277411 on 2026-09-12 at unchanged proof revision '+revision+'. The independent operational audit binds all 137 inputs, original artifact digests, fourteen standard-three axiom checks and both actual isolation/rejection-control suites. Canonical status is Lean verified. The stronger all-matching recurrence and existence at every admissible order are outside the formal scope.'
manifest['review']['status']='agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes']='Both independent statement approvals preceded implementation. Both final referees read the complete original source and proof, freshly re-elaborated eight modules/inspection commands, and audited actual mathematical types and dependencies. All fourteen source and seven additional public kernel assertions per referee passed; each traversed all 49 reached project declarations. The standard-three transitive axioms are propext, Classical.choice and Quot.sound. The seven deliberate Challenge placeholders remain isolated. LeanCert performs actual kernel trust auditing only; no interval certificate is claimed. Local macOS reviews used ten clean exact pinned dependency caches. Actual Linux run 34718277411 at revision '+revision+' matched all seven exports, replayed the solution in the default kernel and passed both real control sets. Independent agent /root/formal_review_standards audited original ZIP bytes, complete raw logs, all 137 inputs, ten fresh dependency clones and 8690 official Mathlib cache artifacts; no full dependency-source rebuild is claimed. The nested Bubblewrap executable was denied UID-map creation before its inner write. Operational report SHA256 017e2a22ac88d153a311c7ef344fe0ac0b8d415f926d046da649e210585c53ac and outer evidence manifest a9dfe074bd299c6826ffe7367f30c5154cf58440a4f88071b8a61ff27eda8aa1 bind 255 files plus the outer manifest, including every nested manifest. Publication changes only this manifest and project README among the 137 verified inputs; all 135 others and all 256 operational evidence files remain identical. The historical statement-stage README, phase labels, metadata snapshots and all four review report hashes are preserved. Relevant Tau Ceti rubrics are adapted to NLA scope; no external human peer review, official endorsement or historical-priority certification is claimed.'
manifest['review']['linux_verification']['status']='passed; independently audited'
manifest['review']['linux_verification']['note']='Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411 at '+revision+'. All seven exports, fourteen standard-three reports, actual default-kernel replay and both control sets passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md and EVIDENCE-MANIFEST.json. Original project ZIP SHA256 8e64089e94c2953d4fae093162b41a3f36540f1888b6f6cd48a11c1dc9a5cc19; control ZIP SHA256 fdc1eddcbe4c3be6e7747fb87de935597b11706a2eadcec35f6a40226028140a.'
mp.write_text(header+'\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))

resolved=(repo/'RESOLVED.md').read_text();title='### ✅ FR-12 - the Hadamard counting conjecture is false - George Stepaniants';start=resolved.index(title);end=resolved.index('\n### ',start+len(title));block=resolved[start:end]
old='Substantial AI assistance is disclosed; this is informal agent review, not human peer review or formal verification.'
assert old in block;block=block.replace(old,'Substantial AI assistance is disclosed. That original review was informal; the later formal verification is documented below. External human peer review is not claimed.',1)
block=block.rstrip()+'''

**Lean verified - 2026-09-12.** The full original counting conjecture is refuted by
[seven checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean/Solution.lean).
**Mathematical proof and Lean formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with
substantial AI-agent assistance. The formal permutation-indexed injection proves
$m!H(m)^2\le H(2m)$ and the identical source power-of-two lower bound; the stronger informal
$(2m-1)!!$ recurrence is outside the exports. Ferber, Jain and Zhao retain the original
conjecture and prior-upper-bound credit. See the
[canonical verification evidence](frames-and-matrix-designs/FR-12/README.md#lean-proof-and-verification-evidence---2026-09-12),
[two statement and two final proof reviews](frames-and-matrix-designs/FR-12/lean/reviews/),
[successful Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411)
and [independent operational audit](frames-and-matrix-designs/FR-12/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md).
All 137 submitted input hashes, actual default-kernel replay, standard-three axioms and real
rejection controls were checked. LeanCert audits kernel trust; no numerical interval
certificate or external human peer review is claimed.

'''
resolved=resolved[:start]+block+resolved[end:];(repo/'RESOLVED.md').write_text(resolved)
(pub/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'prepared':True,'before_counts':dict(counts),'verified_input_count':len(pre['verified_inputs']),'evidence_count':len(pre['operational_files'])},indent=2))
