"""IE23 publication wording only; proof and executed evidence are immutable."""
from pathlib import Path
import copy, hashlib, json, yaml

P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
base=json.loads((E/'baseline.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name,h in base['candidate_inputs'].items(): assert sha(P/name)==h,name
revision='a40e5608f61dd4086708cb2e03901ffd01e4c0a9'
proof='https://github.com/sgstepaniants/OpenProblemsInNLA/tree/'+revision+'/linear-systems-and-elimination/IE-23/lean'
solution=proof.replace('/tree/','/blob/')+'/Solution.lean'
run='https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725525250'
aff='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'

notice=f'''## Lean proof and verification evidence - 2026-09-12

**The complete original uniqueness conjecture is Lean verified, with a negative answer.** The [proof at revision a40e560]({proof}) uses the unchanged rational $`2\\times3`$ example at $`p=4`$. Two distinct right inverses attain the same actual induced norm $`\\sqrt{{\\sqrt{{2}}}}`$ and are global minimizers over **every complex right inverse**. The formalization proves genuine matrix rank and inverse identities, real-power and Euclidean-norm bounds, and the actual supremum over all nonzero complex inputs. The generic norm semantics cover every original dimension and finite real $`p>2`$; no additional boundedness or minimality premise is assumed.

**Lean formalization:** George Stepaniants, {aff}, with AI-agent assistance. **Matthew J. Colbrook** retains mathematical authorship of the resolution; **Ivan Dokmanić and Rémi Gribonval** retain credit for the underlying example and original uniqueness question.

The eight [checked exports]({solution}), each with prefix `NLA.IE23.`, are:

- `inducedNorm_semantics`: actual nonzero-input supremum and all-input norm inequality.
- `witness_matrix_identities`: full row rank, true inverse, both right inverses and distinctness.
- `fourth_power_norm_control`: exact real-power identities and universal complex-vector bound.
- `witness_action_identities`: actual actions and the bound for every right-inverse competitor.
- `witness_attainment`: a genuine nonzero vector attains both norm ratios.
- `witness_norms`: both actual suprema equal the positive fourth root of two.
- `witness_global_minimizers`: both matrices globally minimize the entire feasible norm set.
- `not_rightInverseUniqueConjecture`: the full original universal assertion is false.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Ubuntu run 34725525250]({run}) matched all eight declarations with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and operational audit](lean/verification/linux-2026-09-12/) bind all 190 submitted inputs and both actual isolation/rejection-control suites. All 16 [internal/public axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use exactly `propext`, `Classical.choice` and `Quot.sound`. The proof author performed the operational inspection; the coordinator, independently of that author, [accepted the actual evidence](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json). These operational roles are separate from the two mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits the kernel trust of this pure exact proof; there is **no numerical interval certificate**. The $`p=4`$ sum-of-squares argument avoids approximate norm calculations and interval subdivision. The source's stronger all-$`p`$ formulas, complete minimizer classifications and higher-dimensional families retain their manuscript and informal-review scope; the eight exports give the complete original negative answer. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml) and [dependency pins](lean/lake-manifest.json). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \\
  linear-systems-and-elimination/IE-23/lean \\
  /absolute/path/to/nla-lean-tools
```

'''
canonical=(E/'archive/README.canonical-before.md').read_text()
canonical=canonical.replace('**Status:** Solved','**Status:** Lean verified',1).replace('**Last checked:** 2026-09-11','**Last checked:** 2026-09-12',1)
old='This is independent agent verification, not external human peer review or formal proof-assistant certification; no novelty or priority claim is made.'
new='That original review was informal; the later Lean verification of the canonical negative answer is documented below. External human peer review, novelty and priority are not claimed.'
assert old in canonical;canonical=canonical.replace(old,new,1)
canonical=canonical.replace('## Problem statement\n',notice+'## Problem statement\n',1)
(P.parent/'README.md').write_text(canonical)

readme=(E/'archive/README.linux-candidate.md').read_text()
readme=readme.replace('# IE-23 - complete Lean proof, Linux verification pending','# IE-23 - Lean verified',1)
old='Actual Linux sandboxed Comparator/default-kernel verification, its controls and independent operational audit are still pending. The canonical entry remains **Solved**.'
new=f'Actual [Ubuntu run 34725525250]({run}) verified all eight exports at immutable revision `{revision}`, with default-kernel replay and both real control suites. The proof author\'s operational inspection was separately accepted by the coordinator. The canonical entry is **Lean verified**.'
assert old in readme;readme=readme.replace(old,new,1)
readme=readme.replace('records scope, attribution, automation, reviews and the pending Linux gate.','records scope, attribution, automation, reviews and the successful Linux verification.',1)
old='After the candidate has an immutable Git revision, use the [shared workflow]'
new=f'For the exact executed source, check out [immutable revision a40e560]({proof}). Use the [shared workflow]'
assert old in readme;readme=readme.replace(old,new,1)
actual=f'''## Actual Ubuntu execution and accepted evidence

[Run 34725525250]({run}) completed successfully at `{revision}`. The [project receipt](verification/linux-2026-09-12/artifacts/lean-IE-23/verify-20260912T233011Z-4151/result.json) binds the exact 190-file Git input tree and all eight exports. The genuine Comparator matched both environments with no definition exceptions and replayed the solution in Lean's default kernel. All sixteen internal/public axiom reports contain the standard three axioms. The eight intentional Challenge placeholders remain isolated.

The harness took a fresh committed-source snapshot and cloned all ten dependencies at their pinned revisions. It reused **8690 official Mathlib cache files**; this was not a full dependency-source rebuild. The recorded 2384/2394 Challenge/Solution job counts are graph sizes. Seven project mathematical modules and Solution were freshly elaborated. The shared checker/exporter and Landrun binaries were built from the pinned tool sources. Both the standalone and project jobs exercised real non-root build/export isolation, kernel regressions, Comparator mismatches and the additional admitted/native-proof rejections. Nested Bubblewrap was denied UID-map creation before any inner write; no broader claim is inferred.

The [operational report](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [330-file manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) retain both original GitHub artifact ZIPs, metadata, complete run-log ZIP, source snapshots, checker pins and unmodified logs; the outer manifest is the 331st file and all nested manifests are included. The original project ZIP digest is `bc1fceb8cc81b8c3f7a4c938b3208fc2727fa4f3895dd4c70f5ec3e01f480271`; the control ZIP digest is `f8908adc9b1840cf4d8b9350aa904e8adf160d1d58f696be831cae3d2d191978`.

**Operational inspector `/root/leancert_examples` authored the proof.** The coordinator `/root`, independent of that author and previously final mathematical referee 2, separately [accepted the actual evidence](verification/root-operational-2026-09-12/ROOT-CHECKS.json). The [root evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json) binds that acceptance. Publication preparer `/root/solved_statement_inventory` previously served as independent mathematical referee 1. None of these packaging or operational roles is an additional mathematical review. No new proof build or Linux run is claimed for the refreshed publication wrappers.

'''
readme=readme.replace('## Independent reviews and historical records\n',actual+'## Independent reviews and historical records\n',1)
start=readme.index('All statement-stage documents are historical records of 12 September 2026.')
readme=readme[:start]+'''All statement-stage documents remain historical records of 12 September 2026. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md), [PROOF_MAP.md](PROOF_MAP.md), earlier handoffs and referee reports preserve their original phase-specific wording. Their pending-work statements are superseded by the dated evidence above. The original statement README is retained at [README.statement.md](verification/linux-candidate-2026-09-12/README.statement.md). All other 103 proof-freeze inputs and all eight original source snapshots are unchanged.

Publication changes only this README and the current formalization manifest among the 190 submitted inputs; all other **188 inputs**, all **331 Linux evidence files** and the complete coordinator acceptance evidence remain byte-identical. The exact prior [README](verification/publication-2026-09-12/archive/README.linux-candidate.md) and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml) are archived. Original targets, source manuscripts, pins, code, all eight exports, reviews and the additive configuration supplement are preserved. The successful run remains bound to the immutable candidate revision; the publication handoff separately records wrapper, catalog and rendered-document checks.
'''
(P/'README.md').write_text(readme)

manifest=yaml.safe_load((E/'archive/formalization.linux-candidate.yaml').read_text())
oldmanifest=copy.deepcopy(manifest)
manifest['status']['scope']=f'Complete negative answer to the entire canonical direct induced-norm uniqueness conjecture. The exact p=4 matrices are two distinct global minimizers over all complex right inverses; generic denominator/supremum semantics cover every original domain. All eight exports passed two independent statement reviews, two independent final proof reviews and actual Linux sandboxed Comparator/default-kernel verification in run 34725525250 on 2026-09-12 at unchanged proof revision {revision}. All 190 submitted inputs, sixteen standard-three axiom reports and both actual control suites were operationally inspected by the proof author and independently accepted by the coordinator. Canonical status is Lean verified. Source all-p formulas, full classifications, higher-dimensional families and endpoints remain outside the eight exports.'
manifest['review']['status']='agent-reviewed; Linux-Comparator-and-default-kernel-verified'
manifest['review']['notes']=f'Both statement approvals preceded implementation and include the unchanged Comparator supplement. Both independent final referees freshly elaborated ten commands in private prefixes excluding old IE-23 objects and inspected actual proof terms. Each traversed 93 project declarations; referee1 checked40 dependencies and referee2 checked28 plus12 kernel assertions. All sixteen internal/public axiom reports use exactly propext, Classical.choice and Quot.sound. LeanCert supplies explicit kernel trust auditing of a pure exact proof; no numerical interval certificate. Local macOS reviews reused clean matching dependency objects read-only. Actual Ubuntu run34725525250 at {revision} freshly cloned ten pinned dependencies, reused8690 official Mathlib cache artifacts, built project sources, matched all eight exports with no definition exceptions, replayed them in the default kernel and passed both real control suites. No full dependency-source rebuild is claimed. Nested Bubblewrap was denied UID-map creation before its inner write. Operational inspector /root/leancert_examples authored the proof and is neither independent mathematical referee; coordinator /root independently accepted the actual evidence and had served as final referee2. Publication preparer /root/solved_statement_inventory had served as independent final referee1; packaging is not a third review. Operational report de746fa0bc2d1cf905b9275c9f5f233a043d3fdc55f35deda04f9226c6dd216e and outer3d4685d019c85ba80681551637f43ecf8bfc428a91dc8c985596405f36178da2 bind330files plus itself, preserving every nested manifest. Root acceptance17f33157d63f994a2389d0ad03beaa9627d7c4275b622f6906c8b64dee2dbd16 is bound by root manifestb35250b043bb8ddf2bbbc5c03c20c771b89c15e91f18f2bc5af5495b0f17abe1. Publication archives both prior wrappers and changes only current README/formalization.yaml among190verifiedinputs, preserving188others, all331Linuxevidencefiles, allrootacceptanceevidence,103nonREADMEprooffreezeinputs and8originalsources. Frozen phase labels remain historical. No external human review, official Tau Ceti endorsement or mathematical priority is claimed.'
# Keep the public prose readable, including counts in the detailed provenance note.
for old,new in [('referee1','referee 1'),('referee2','referee 2'),('checked40','checked 40'),('checked28','checked 28'),('plus12','plus 12'),('run34725525250','run 34725525250'),('reused8690','reused 8690'),('outer3d','outer 3d'),('bind330files','bind 330 files'),('acceptance17','acceptance 17'),('manifestb352','manifest b352'),('among190verifiedinputs','among 190 verified inputs'),('preserving188others','preserving 188 others'),('all331Linuxevidencefiles','all 331 Linux evidence files'),('allrootacceptanceevidence','all root acceptance evidence'),('103nonREADMEprooffreezeinputs','103 non-README proof-freeze inputs'),('8originalsources','eight original sources')]:
    manifest['review']['notes']=manifest['review']['notes'].replace(old,new)
manifest['review']['notes']=manifest['review']['notes'].replace('evidence,103','evidence, 103').replace('andeight','and eight')
manifest['review']['linux_verification']['status']='passed; operationally inspected and independently accepted'
manifest['review']['linux_verification']['note']=f'Actual run {run} at {revision}. All eight exports, sixteen standard-three reports, default-kernel replay and both actual control suites passed. See verification/linux-2026-09-12/OPERATIONAL-REVIEW.md and EVIDENCE-MANIFEST.json, and independent coordinator acceptance verification/root-operational-2026-09-12/ROOT-CHECKS.json. Original project ZIP SHA256 bc1fceb8cc81b8c3f7a4c938b3208fc2727fa4f3895dd4c70f5ec3e01f480271; controls ZIP SHA256 f8908adc9b1840cf4d8b9350aa904e8adf160d1d58f696be831cae3d2d191978. Complete original run-log ZIP retained with its independently computed digest.'
allowed=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
a=copy.deepcopy(oldmanifest);b=copy.deepcopy(manifest)
for path in allowed:
    x=a;y=b
    for key in path[:-1]:x=x[key];y=y[key]
    x.pop(path[-1]);y.pop(path[-1])
assert a==b
(P/'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))

resolved=(E/'archive/RESOLVED.before.md').read_text()
start=resolved.index('### IE-23 - Negative resolution\n')
end=resolved.index('\nThe related order-five rook bound',start)
block=resolved[start:end].replace('**Solved.**','**Lean verified.**',1)
block+=f'''\n\n**Lean formalization:** George Stepaniants, {aff}, with AI-agent assistance. **Matthew J. Colbrook** retains mathematical authorship; **Ivan Dokmanić and Rémi Gribonval** retain the underlying example and original-question credit. The [eight exports at revision a40e560]({solution}) prove the actual p=4 norms, global minimality over every complex right inverse and the complete canonical conjecture's negation. The stronger all-p formulas and classifications above retain their manuscript and informal-review scope. [Ubuntu run34725525250]({run}) passed sandboxed Comparator matching, default-kernel replay and both actual control suites with the standard three axioms. LeanCert supplies kernel trust auditing of the pure exact proof, with no interval certificate. The proof author's [operational audit](linear-systems-and-elimination/IE-23/lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) was [independently accepted by the coordinator](linear-systems-and-elimination/IE-23/lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json). See the [project guide](linear-systems-and-elimination/IE-23/lean/README.md) and [manifest](linear-systems-and-elimination/IE-23/lean/formalization.yaml).'''
block=block.replace('Ubuntu run34725525250','Ubuntu run 34725525250')+'\n'
(W/'RESOLVED.md').write_text(resolved[:start]+block+resolved[end:])
print('Prepared canonical notice, project guide, exactly five manifest fields and only IE23 RESOLVED block')
