from pathlib import Path
from datetime import datetime, timezone
import collections, hashlib, json, re, subprocess, yaml

repo = Path('/tmp/nla-lean-mi03-worktree')
entry = repo/'matrix-inequalities-and-norms/MI-03'
project = entry/'lean'
work = Path(__file__).resolve().parent
pub = project/'verification/publication-2026-09-12'
revision = '901ba5ffad3b57557b60c7360df67659d8b8aa21'
base = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
run = 34722618003
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
pre = json.loads((work/'before-integration.json').read_text())
integration = json.loads((work/'integration.json').read_text())
assert git('rev-parse','HEAD').decode().strip() == integration['integration_commit']
for group in ['verified_inputs','operational_files']:
    for name, h in pre[group].items(): assert sha(project/name) == h, name
assert not pub.exists()
pub.mkdir(); (pub/'archive').mkdir()
for source, dest in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    (pub/'archive'/dest).write_bytes((project/source).read_bytes())
canonical = (entry/'README.md').read_text()
target = canonical[canonical.index('## Problem statement'):]
registry = json.loads((repo/'problem_ids.json').read_text())
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)', (repo/p).read_text(), re.M).group(1).strip() for p in registry.values())
before = {'created_utc':datetime.now(timezone.utc).isoformat(), 'verified_revision':revision, 'verified_run':run,
          'base':base, 'integrated_head':integration['integration_commit'], 'all_verified_inputs':pre['verified_inputs'],
          'all_operational_evidence':pre['operational_files'], 'canonical_target_tail_sha256':hashlib.sha256(target.encode()).hexdigest(),
          'other_canonical':{i:sha(repo/p) for i,p in registry.items() if i!='MI-03'},
          'problem_ids_sha256':sha(repo/'problem_ids.json'), 'branch_counts_before':dict(counts)}
(pub/'before.json').write_text(json.dumps(before,indent=2)+'\n')
for name in ['integration.json','integration.log','snapshot.py','before-integration.json']:
    (pub/name).write_bytes((work/name).read_bytes())

section = r'''## Lean proof and verification evidence - 2026-09-12

**The complete original odd-summand conjecture is Lean verified.** The [proof at revision 901ba5f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean) proves that $`k/4`$ is the least member of the full admissible-constant set for every $`k\ge2`$, then identifies its actual real infimum. This includes every odd $`k\ge3`$, with all positive dimensions and every tuple of complex contractions. Genuine principal CFC moduli and Euclidean operator norms are used; no literature inequality is assumed as an unproved premise.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains authorship of the mathematical proof and result; **Jean-Christophe Bourin and Eun-Young Lee** retain the original conjecture and prior-bound credit.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean/Solution.lean), each with prefix `NLA.MI03.`, are:

- `modulus_semantics`: genuine positive square root, square and norm identities.
- `contraction_modulus`: positive modulus defects for every complex contraction.
- `positive_decomposition`: the exact universal Gram-sum and positive-square identity.
- `universal_upper_bound`: admissibility of $`k/4`$ for every $`k\ge2`$.
- `root_of_unity_data`: exact complex roots and their vanishing geometric sums.
- `sharpness_witness`: true moduli, unit operator norms and full sums of the two-dimensional extremizers.
- `sharp_constant`: actual least admissible constant and infimum, for every $`k\ge2`$.
- `odd_contraction_conjecture`: the complete original assertion.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34722618003](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003) matched all eight declarations with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and operational audit](lean/verification/linux-2026-09-12/) bind all 173 input files and both actual isolation/rejection-control suites. All 16 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use exactly `propext`, `Classical.choice` and `Quot.sound`. The operational reviewer also served as final proof referee 1; these roles do not count as a third mathematical referee. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits this exact proof's kernel trust; there is **no numerical interval certificate**. Symbolic identities and all-$`k`$ roots avoid numerical phase approximation or interval subdivision. The source's extra three-dimensional Hermitian extremizers and rank classification are outside these exports; the complete original target is covered. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml) and [dependency pins](lean/lake-manifest.json). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-03/lean \
  /absolute/path/to/nla-lean-tools
```

'''
assert canonical.count('**Status:** Solved') == 1
canonical = canonical.replace('**Status:** Solved  \n','**Status:** Lean verified  \n',1)
canonical = canonical.replace('**Last checked:** 2026-09-11','**Last checked:** 2026-09-12',1)
old = 'The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification.'
assert old in canonical
canonical = canonical.replace(old, 'The draft was AI-assisted. That original review was informal; the later Lean verification is documented below. External human peer review is not claimed.',1)
canonical = canonical.replace('## Problem statement',section+'## Problem statement',1)
assert canonical[canonical.index('## Problem statement'):] == target
(entry/'README.md').write_text(canonical)

readme = (project/'README.md').read_text()
readme = readme.replace('# MI-03 — complete Lean proof, Linux verification pending','# MI-03 — verified sharp constant for sums of contractions',1)
old = readme.split('\n\n')[1]
assert old.startswith('**The complete odd-summand')
new = '''**The complete odd-summand sharp-constant conjecture is Lean verified, with all eight reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals followed. The unchanged proof at [revision 901ba5f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean) passed actual Linux sandboxed Comparator/default-kernel verification in [run 34722618003](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003) on 12 September 2026. The [independent operational audit and original artifacts](verification/linux-2026-09-12/) bind all 173 submitted inputs. The [canonical entry](../README.md) records the complete verified scope.'''
readme = readme.replace(old,new,1)
readme = readme.replace('**Bourin and Lee** retain the original conjecture and prior-bound credit.','**Jean-Christophe Bourin and Eun-Young Lee** retain the original conjecture and prior-bound credit.',1)
readme = readme.replace('## Independent reviews and remaining gates','## Independent reviews and Linux evidence',1)
old = '''Actual sandboxed Linux Comparator/default-kernel replay, its controls, an independent operational audit and publication review remain required by the [shared workflow](../../../docs/lean/README.md) and [harness](../../../tools/lean/HARNESS.md). No project-specific Linux result or immutable submitted revision is claimed yet.

Candidate packaging archives the original frozen README at [README.statement.md](verification/candidate-2026-09-12/README.statement.md). Only the current README changes among the 101 proof-freeze inputs. All other 100 inputs and all eight original source files remain identical; every frozen mathematical statement, proof, pin, configuration and earlier review record is preserved. The current guide describes completion; frozen statement-stage labels remain historical.'''
new = '''The later Linux run freshly cloned all ten dependencies at their exact pinned revisions and used 8690 official Mathlib cache artifacts before building the submitted project source. The Challenge and Solution build graphs completed with 2714 and 3041 jobs respectively; these are graph counts, not claims of full dependency-source rebuilds. Both the project job and separate checker job passed the actual isolation and rejection controls. The nested Bubblewrap executable was denied UID-map creation before its inner write; the probe is not a general sandbox security guarantee.

The actual Comparator matched all eight declarations, with no definition exceptions, and replayed the solution in Lean's default kernel. Both suites exercised three raw-kernel controls, five Comparator fixtures and the admission/native-execution negative controls. All sixteen internal/public transitive axiom checks contain exactly the standard three. The [complete Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) binds 303 files plus itself, including every nested manifest, both original artifact ZIPs, complete raw logs and exact input/tool-source snapshots.

The operational reviewer, `/root/formal_review_standards`, is also statement referee 1 and final proof referee 1. The two independent mathematical referees remain two distinct agents; operational review is a separate check performed by one of them. The proof-implementing agent `/root` is neither independent final referee. These checks do not assert external human peer review, official Tau Ceti endorsement or source-author endorsement.

Use the [shared workflow](../../../docs/lean/README.md) on a correctly configured [non-root Linux host](../../../tools/lean/HARNESS.md). From the immutable verified revision's repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \\
  matrix-inequalities-and-norms/MI-03/lean \\
  /absolute/path/to/nla-lean-tools
```

The exact historical statement-stage README remains at [README.statement.md](verification/candidate-2026-09-12/README.statement.md). All other 100 proof-freeze inputs remain byte-identical. Publication changes only this README and the current formalization manifest among the 173 Linux-verified inputs; all other 171 inputs and all 304 retained Linux evidence files are unchanged. The exact prepublication [README](verification/publication-2026-09-12/archive/README.linux-candidate.md) and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml) are archived. All eight original source snapshots are retained; only the canonical page and its generated documents gain the verification notice. The original mathematical target and source proof are unchanged. The successful run is bound to the immutable proof revision; no new run over these publication wrappers is claimed. Frozen phase labels and earlier metadata remain historical.'''
assert old in readme
readme = readme.replace(old,new,1)
(project/'README.md').write_text(readme)

mp = project/'formalization.yaml'
header = mp.read_text().splitlines()[0]
manifest = yaml.safe_load(mp.read_text())
manifest['status']['scope'] = 'Complete affirmative answer to the full canonical odd-summand conjecture, via IsLeast of the entire admissible set at k/4 for every k≥2 and equality of its actual real infimum. All eight exports passed two independent statement reviews, two independent final proof reviews and actual Linux sandboxed Comparator/default-kernel verification in run 34722618003 on 2026-09-12 at unchanged proof revision '+revision+'. The independent operational audit binds all 173 inputs, original artifact digests, sixteen standard-three axiom reports and both actual isolation/rejection-control suites. Canonical status is Lean verified. Additional three-dimensional Hermitian extremizers and rank classification remain outside these exports.'
manifest['review']['status'] = 'agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes'] = 'Both independent statement approvals preceded implementation. Final reviewers freshly elaborated the actual proof in separate prefixes excluding old project objects and inspected material proof dependencies. All sixteen internal/public kernel assertions and transitive axiom reports allow only propext, Classical.choice and Quot.sound. LeanCert supplies explicit kernel trust auditing only; no numerical interval certificate is claimed. Challenge placeholders remain isolated from Solution. Local macOS reviews used matching pinned dependency caches. Actual Linux run 34722618003 at '+revision+' freshly cloned ten pinned dependencies, reused 8690 official Mathlib cache artifacts, built the project sources, matched all eight exports with no definition exceptions, replayed them in the default kernel and passed both real control suites. No full dependency-source rebuild is claimed. The nested Bubblewrap executable was denied UID-map creation before its inner write. Independent agent /root/formal_review_standards audited all 173 submitted inputs, original artifact ZIPs and logs, exact pins/tool-source lock and default-kernel/control results. This operational reviewer also served as statement referee 1 and final proof referee 1; it is not a third mathematical referee. The implementing agent /root is neither independent final referee. Operational report SHA256 0c582ae4b9271ce89cd9484a45d380f3cfa8cab60595a7986debcaa67c084e30 and outer evidence manifest ecbdf4f208c72dd016442ca7dba5fd925b5c51286719454e5a58563460a610d9 bind 303 files plus the outer manifest, including all nested manifests. Publication archives both exact prior wrappers and changes only the current README and formalization.yaml among the 173 verified inputs; all 171 others and all 304 Linux evidence files remain identical. All 100 non-README proof-freeze inputs, the historical README archive and original source snapshots are retained. Frozen phase labels and earlier metadata remain historical. No external human peer review, official Tau Ceti endorsement or historical priority is claimed.'
manifest['review']['linux_verification']['status'] = 'passed; independently audited'
manifest['review']['linux_verification']['note'] = 'Actual run https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003 at '+revision+'. All eight exports, sixteen standard-three reports, actual default-kernel replay and both control suites passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md and EVIDENCE-MANIFEST.json. Original project ZIP SHA256 ca9ae612e2b9daef185d7d23fcfe2930c6a73b3cdbefa2b77bb24108ffc74e8d; control ZIP SHA256 55dd2ca9c189c2b5fda8d8785cbf0177a74f77cdc26d0f12f03a3c4c11526f8d. Complete original run-log archive is retained with its separately computed digest.'
mp.write_text(header+'\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))

resolved = (repo/'RESOLVED.md').read_text()
title = '#### MI-03 — affirmative result'
start = resolved.index(title); end = resolved.index('\n#### ',start+len(title))
block = resolved[start:end]
block = block.replace(title,title+' by Matthew J. Colbrook; Lean formalization by George Stepaniants',1)
block = block.rstrip()+r'''

**Lean verified - 2026-09-12.** The [eight checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean/Solution.lean) prove the complete original odd-summand conjecture, via the stronger least admissible constant $`k/4`$ for every $`k\ge2`$. The actual CFC moduli, Euclidean operator norms, all complex contraction tuples and real infimum of the entire admissible set are retained; the universal upper bound is proved internally. **Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance. Matthew J. Colbrook retains mathematical proof/result credit; Jean-Christophe Bourin and Eun-Young Lee retain the conjecture and prior-bound credit. See the [canonical verification evidence](matrix-inequalities-and-norms/MI-03/README.md#lean-proof-and-verification-evidence---2026-09-12), [statement and final proof reviews](matrix-inequalities-and-norms/MI-03/lean/reviews/), [successful Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003) and [independent operational audit](matrix-inequalities-and-norms/MI-03/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md). All 173 submitted inputs, sixteen standard-three axiom reports, actual default-kernel replay and real controls were checked. The operational reviewer also served as final proof referee 1. LeanCert audits this exact proof's kernel trust; no numerical interval certificate or external human peer review is claimed. The source's additional three-dimensional Hermitian extremizers and rank classification are outside the formalized exports.

'''
resolved = resolved[:start]+block+resolved[end:]
(repo/'RESOLVED.md').write_text(resolved)
(pub/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'prepared':True,'integrated_head':integration['integration_commit'],'before_counts':dict(counts),'verified_inputs':len(pre['verified_inputs']),'operational_files':len(pre['operational_files'])},indent=2))
