from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, yaml

repo=Path('/tmp/nla-lean-ie23-worktree')
project=repo/'linear-systems-and-elimination/IE-23/lean'
candidate=project/'verification/linux-candidate-2026-09-12'
base='f41f1f9ffa2171550d4bb795862c6170c4f26070'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *args:subprocess.check_output(['git',*args],cwd=repo)
assert git('rev-parse','HEAD').decode().strip()==base
assert git('diff','--name-only')==b'' and git('diff','--cached','--name-only')==b''
assert not (project/'formalization.yaml').exists()
proof_freeze=project/'reviews/proof-freeze.json'
assert sha(proof_freeze)=='8ed8f46ea66c9e420156d99840e4e24e78cf8207a9e415cc7c26f6f9739e5fe8'
freeze=json.loads(proof_freeze.read_text());assert len(freeze['files'])==104 and len(freeze['source_files'])==8
for name,r in freeze['files'].items():
    assert sha(project/name)==r['sha256'] and (project/name).stat().st_size==r['bytes'],name
for name,h in freeze['source_files'].items():
    assert sha(repo/name)==h and hashlib.sha256(git('show',base+':'+name)).hexdigest()==h,name
    assert sha(project/'reviews/source-snapshot'/name)==h,name
report_hashes={
    'reviews/statement-referee-1.md':'d2f3669ada22f985ce66681a1b763d0fc722d1938b9c2a35b27792f7fc418270',
    'reviews/statement-referee-2.md':'dda8d5d5dc194371818ecef9fa4e1a20d52dbadc7b8f998dff4a815cfbd4f758',
    'reviews/proof-referee-1.md':'4aded9a6adfc4723941bae2ac8c4ae0c1ad4bdef7136dd3a285068ae1f68d4d2',
    'reviews/proof-referee-2.md':'0b6f2f6ed1aa4505da7ceb63d33470822914820904a4b0fee309f69ba314c008'}
for name,h in report_hashes.items():assert sha(project/name)==h,name
evidence_hashes={
    'reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json':'bb232d4c5a8c2a8fb75238547cbc9646a99ab8f3904286152f52963140132748',
    'reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json':'020a62b026a9d00b6e41b50feefd468979d87a74e3384a688a1bb449b49a2847',
    'reviews/statement-referee-1-evidence/EVIDENCE-MANIFEST.json':'828c4e8b8f6876bd3a5ead7931eb597f3f1259c21e0a699b1f8d191bf6bc666e',
    'reviews/statement-referee-2-root-evidence/EVIDENCE-MANIFEST.json':'4f7eaad1c45375ab077b7d6690044c99dbe3b11f9051273b7b2ebfbef4c49ef7'}
evidence_records={}
for name,h in evidence_hashes.items():
    path=project/name;assert sha(path)==h,name;d=json.loads(path.read_text())
    for rel,r in d['files'].items():
        f=path.parent/rel
        assert f.resolve().is_relative_to(project.resolve()) and f.is_file() and not f.is_symlink(),rel
        assert sha(f)==r['sha256'] and f.stat().st_size==r['bytes'],rel
    actual={str(f.relative_to(path.parent)) for f in path.parent.rglob('*') if f.is_file() and f!=path}
    internal={rel for rel in d['files'] if not rel.startswith('../')}
    assert actual==internal,(name,actual^internal)
    if 'review' in d:
        r=d['review'];assert sha(path.parent/r['path'])==r['sha256'] and (path.parent/r['path']).stat().st_size==r['bytes']
    evidence_records[name]={'sha256':h,'bound_file_count':len(d['files']),'internal_file_count':len(internal),'complete_internal_inventory':True}
assert sha(project/'reviews/statement-config-supplement.json')=='dafd6645aa017c543dd4eb9f60633b47a2035f090d58955525a3d6c41156141a'
config=json.loads((project/'comparator.json').read_text())
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert len(config['theorem_names'])==8
headers=re.findall(r'^theorem\s+(\w+)\b',(project/'Solution.lean').read_text(),re.M)
assert ['NLA.IE23.'+name for name in headers]==config['theorem_names']
prefix=str(project.relative_to(repo))+'/'
paths=[p for p in git('ls-files','--others','--exclude-standard','--',prefix).decode().splitlines()
       if not p.startswith(str(candidate.relative_to(repo))+'/')]
inputs={p.removeprefix(prefix):{'sha256':sha(repo/p),'bytes':(repo/p).stat().st_size} for p in paths}
assert len(inputs)==166
candidate.mkdir(exist_ok=True)
if (candidate/'README.statement.md').exists():
    assert (candidate/'README.statement.md').read_bytes()==(project/'README.md').read_bytes()
else:
    (candidate/'README.statement.md').write_bytes((project/'README.md').read_bytes())
before={'created_utc':datetime.now(timezone.utc).isoformat(),'base':base,'preexisting_project_inputs':inputs,
        'proof_freeze_sha256':sha(proof_freeze),'proof_frozen_inputs':freeze['files'],'source_inputs':freeze['source_files'],
        'report_sha256':report_hashes,'review_evidence':evidence_records,'config_sha256':sha(project/'comparator.json'),
        'supplement_sha256':sha(project/'reviews/statement-config-supplement.json'),
        'canonical_status':'Solved','root_tracked_diff_before':git('diff','--name-only').decode()}
if (candidate/'inputs-before.json').exists():
    prior=json.loads((candidate/'inputs-before.json').read_text())
    assert {k:v for k,v in prior.items() if k!='created_utc'}=={k:v for k,v in before.items() if k!='created_utc'}
else:
    (candidate/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')

readme='''# IE-23 - complete Lean proof, Linux verification pending

**The complete original induced-norm uniqueness conjecture has a proved negative answer in Lean, with all eight reviewed exports.** Two independent statement approvals, including the exact additive Comparator supplement, preceded implementation. Two independent final proof reviewers approved the completed source after their own fresh elaboration and actual-term audits. Actual Linux sandboxed Comparator/default-kernel verification, its controls and independent operational audit are still pending. The canonical entry remains **Solved**.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains credit for the mathematical resolution. **Dokmanić and Gribonval** retain attribution for the underlying rational matrix in their Example 4.1. No new mathematical priority or source-author endorsement is claimed. The implementing agent `/root/leancert_examples` is neither independent final referee; the coordinator `/root` served as independent statement and final proof referee 2.

## Complete target and proved scope

The full [canonical problem](../README.md) quantifies every original dimension 1≤m<n, every complex full-row-rank matrix A, every finite real p>2 and every distinct complex right inverse. It uses the direct induced p-to-2 norm, with the genuine Euclidean numerator, exact real-power denominator and actual supremum over every nonzero complex input. [Definitions](NLA/IE23/Definitions.lean) preserves this entire universal assertion, including the actual matrix rank and Moore-Penrose formula A* (AA*)⁻¹.

The exact source matrices at m=2, n=3 and p=4 give a full counterexample:

```
A = [[1,1,0], [1,0,1]]
B = (1/3) [[1,1], [2,-1], [-1,2]]
X = [[0,0], [1,0], [0,1]]
z = (1,-1), c = sqrt(sqrt(2))
```

[Norms](NLA/IE23/Norms.lean) proves the generic denominator positivity, nonempty/bounded ratio set and actual least-upper-bound property on every original domain, then the all-input operator inequality including zero. [Matrices](NLA/IE23/Matrices.lean) proves actual invertibility, rank, B=A†, both right-inverse equations and distinctness. These are conclusions; no extra boundedness, invertibility or minimization premise is assumed.

[FourthPower](NLA/IE23/FourthPower.lean) proves the true fourth-root and real-power identities and the universal complex-vector norm bound from the exact sum of squares (a²−b²)²≥0. [Actions](NLA/IE23/Actions.lean) proves both norming-vector attainments and the all-competitor identity: every complex right inverse Y satisfies Yz=(t,1−t,−1−t), so its squared Euclidean norm is 2+3|t|². [Minimizers](NLA/IE23/Minimizers.lean) identifies the actual suprema of B and X with c, proves they are both global minimizers over **all complex right inverses**, and establishes the genuine least feasible norm value. [Proof](NLA/IE23/Proof.lean) concludes the negation of the entire original conjecture.

The source's all-p formulas, full minimizer classifications, higher-dimensional families, smallest-dimension classification, endpoints and separate product-norm objective are outside the eight formal exports. The admissible p=4 case suffices for the complete original negative answer. All original source bytes and attribution are retained.

[Solution](Solution.lean) exports these exact [Challenge](Challenge.lean) signatures, each with prefix `NLA.IE23.`:

- `inducedNorm_semantics`
- `witness_matrix_identities`
- `fourth_power_norm_control`
- `witness_action_identities`
- `witness_attainment`
- `witness_norms`
- `witness_global_minimizers`
- `not_rightInverseUniqueConjecture`

## Exact computation and LeanCert

**LeanCert performs explicit kernel trust auditing of a pure exact proof. There is no numerical interval certificate.** Choosing p=4 reduces the only needed norm comparison to a sum of squares, avoiding interval subdivision, approximate norms and spectral enclosures. Real power and nonnegative-square bridges justify the unsquared inequalities. The exact diagnostic scripts are supplementary transcription/algebra checks, not proof oracles.

All sixteen internal/public `#assert_trust kernel` commands and transitive axiom reports allow exactly `propext`, `Classical.choice` and `Quot.sound`. The completed solution has no admission, custom axiom or native execution trust. The eight deliberate Challenge placeholders remain isolated and are never imported by Solution. [Comparator](comparator.json) selects every public export, with no definition exceptions and only the standard three axioms.

The project pins Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`; [lake-manifest.json](lake-manifest.json) pins all ten dependencies. The [actual v0.4 manifest](formalization.yaml) records scope, attribution, automation, reviews and the pending Linux gate.

## What ran and how to reproduce

The author and both independent final referees each completed ten fresh direct Lean commands: seven mathematical modules, Solution, their own actual-term inspector and separately invoked Challenge. All completed modules passed without warnings; only the eight intentional Challenge placeholders warned. Each audit reached 93 project declarations. The author required 38 retained mathematical dependencies, referee 1 required 40, and referee 2 independently required 28 and added twelve kernel assertions. Their exact scripts, object/source paths, logs and receipts are retained in the linked evidence.

These were **macOS source re-elaborations**, using clean matching MI-22 dependency objects read-only because of limited disk space. Every IE-23 project object was compiled into a new private prefix, excluding all prior project objects. They were not local Lake invocations, full dependency-source rebuilds or Linux Comparator runs. The packaging task does not repeat these proof checks or download dependencies.

For a normal checkout with its own dependencies, the explicit project proof command is:

```
lake build Solution
```

The deliberately frozen default is Challenge; plain `lake build` therefore checks statements. The retained author and referee runners record the exact local source/pin/object paths used in their private-prefix checks. Their integrity assertions bind the historical README and evidence at that phase. Reproducing those historical runners requires an isolated copy of those frozen inputs and their recorded local paths; they are not generic commands to rerun over refreshed publication wrappers. The normal proof command above and the shared Linux workflow below apply to the current candidate.

After the candidate has an immutable Git revision, use the [shared workflow](../../../docs/lean/README.md) on a correctly configured [non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \\
  linear-systems-and-elimination/IE-23/lean \\
  /absolute/path/to/nla-lean-tools
```

## Independent reviews and historical records

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Exact statement-gate configuration: [supplement](reviews/statement-config-supplement.md) and [record](reviews/statement-config-supplement.json).
- Final proof referee 1: [report](reviews/proof-referee-1.md) and [evidence](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json).
- Final proof referee 2: [report](reviews/proof-referee-2.md) and [evidence](reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json).
- [Proof-start record](verification/proof-start.json), [author completion](reviews/proof-completion.md), [author execution](verification/final-author/fresh-checks.json) and [complete proof freeze](reviews/proof-freeze.json).

The referees apply the [pinned Tau Ceti adaptation](../../../docs/lean/REVIEW.md), including original-target fidelity, actual definitions and hypotheses, proof quality, library reuse, API, documentation and attribution. These are independent AI-agent reviews, not external human peer review or official Tau Ceti endorsement. Schiffer and Forsythe are credited as campaign organization/tooling examples; no mathematical result from those projects is assumed.

All statement-stage documents are historical records of 12 September 2026. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md), [PROOF_MAP.md](PROOF_MAP.md), earlier handoffs and referee reports preserve their original phase-specific wording. Their pending-work statements are superseded only by the dated later evidence described here. The exact original README is archived at [README.statement.md](verification/linux-candidate-2026-09-12/README.statement.md). Only this README changes among the 104 proof-freeze inputs; all other 103 inputs, all eight original sources/snapshots, both final review evidence sets and the exact configuration supplement are unchanged. The new formalization manifest and candidate preservation evidence are additive.

Actual Linux default-kernel/Comparator execution and controls, an independent operational audit, and publication review remain required before canonical promotion. No project-specific Linux success, immutable submitted proof revision, or Lean-verified canonical status is claimed yet.
'''
(project/'README.md').write_text(readme)

axioms=['propext','Classical.choice','Quot.sound']
scopes=[
    'Generic actual nonzero-input supremum semantics for every original domain: denominator positivity, nonempty bounded ratio set, IsLUB, nonnegativity and all-input inequality including zero.',
    'Exact full row rank, genuine matrix inverse and Moore-Penrose formula, both right inverses, distinctness and Gram identities for the source witness.',
    'Exact positive fourth-root/real-power identities and the universal unsquared norm comparison for all complex two-vectors at p=4.',
    'Actual actions on every complex input and the squared Euclidean lower-bound identity for every complex right-inverse competitor.',
    'Actual nonzero norming vector and both attained ratios, with true denominator and Euclidean numerators.',
    'Equalities of the actual nonzero-input suprema of both distinct feasible matrices with the positive fourth root of two.',
    'Both matrices are global minimizers over all complex right inverses, and their common norm is IsLeast of the entire feasible value set.',
    'Unconditional negation of the complete original all-dimension, all-full-row-rank-complex-matrix, finite-real-p>2 strict uniqueness conjecture.'
]
manifest={
 'version':'v0.4',
 'project':{'name':'IE-23: nonuniqueness of induced-norm-minimizing right inverses',
  'description':'Complete negative answer to the original direct induced p-to-2 norm uniqueness conjecture, with two distinct global minimizers at the exact admissible p=4 witness.',
  'authors':['George Stepaniants'],
  'affiliations':{'George Stepaniants':'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'},
  'responsible_maintainers':['George Stepaniants'],'license':'Apache-2.0'},
 'repository':{'role':'substantive-development'},
 'sources':[
  {'title':'IE-23 - uniqueness of the right inverse minimizing an induced p-to-2 norm',
   'id':'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/'+base+'/linear-systems-and-elimination/IE-23/README.md',
   'type':'web-post','location':'Complete canonical problem statement','relationship':'formalizes','author_endorsement':'not-contacted',
   'note':'Every 1≤m<n, full-row-rank complex A, finite real p>2 and distinct complex right inverse, with the genuine direct induced norm and Moore-Penrose formula. The entire universal conjecture is negated.'},
  {'title':'Nonuniqueness of induced-norm-minimizing right inverses','authors':['Matthew J. Colbrook'],
   'id':'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/'+base+'/references/colbrook-recovered-2026-09-11/manuscripts/IE-23.tex',
   'type':'manuscript','location':'Theorem 1 and global-optimality argument, specialized to p=4; SOURCE_CORRESPONDENCE.md and PROOF_MAP.md give exact scope',
   'relationship':'adapts','author_endorsement':'not-contacted',
   'note':'Colbrook retains the mathematical resolution. The rational matrices are unchanged. The p=4 case gives the full canonical negative answer. All-p formulas, full minimizer classifications, higher-dimensional families, smallest-dimension classification and endpoints are outside these eight exports.'},
  {'title':'Beyond Moore-Penrose Part I: Generalized Inverses that Minimize Matrix Norms','authors':['Ivan Dokmanić','Rémi Gribonval'],
   'id':'https://arxiv.org/abs/1706.08349v2','type':'preprint',
   'location':'Example 4.1, equations (51)-(53), pp.16-17; Corollary 4.2(3) and Remark 4.1, p.18',
   'relationship':'background','author_endorsement':'not-contacted',
   'note':'Retains attribution for the underlying rational A and Moore-Penrose example and the original direct-inverse uniqueness question. Its separate product objective is outside the canonical target. No unproved literature inequality is assumed by the Lean proof.'}],
 'related_formalizations':[
  {'id':'https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof','relationship':'other',
   'note':'Campaign organization and pinned kernel-trust/Comparator workflow example; shared tool reuse and licenses are retained. No Forsythe mathematical theorem is assumed.'},
  {'id':'https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1','relationship':'other',
   'note':'Statement/analytic-proof separation example studied in the campaign. No Schiffer mathematical theorem is imported.'}],
 'automation':{'methods':[{'method':'agent','framework':'OpenAI Codex',
   'tool_setup':'Multiple agents; two statement approvals including the exact additive Comparator supplement before implementation, then two independent final proof reviews with private-prefix elaboration and actual compiled dependency audits.',
   'prompting_notes':'Preserve the full original complex-matrix, dimension and finite-real-p quantifiers, actual Euclidean and p norms, matrix rank/inverse, nonzero-input supremum and all-complex global competitor set. Specialize the unchanged source counterexample to p=4; prove nonvacuity and unsquared norm bridges internally. Use exact algebra and LeanCert kernel trust auditing, without an artificial interval certificate.'}],
   'notes':'AI-assisted formalization requested by George Stepaniants. The implementing agent /root/leancert_examples is neither independent final referee. Coordinator /root is independent final referee 2; /root/solved_statement_inventory is independent final referee 1. Candidate documentation is prepared by /root/formal_review_standards and is not an additional mathematical review. No external human review, official Tau Ceti endorsement, model identity, measured cost or priority is claimed.'},
 'status':{'scope':'Complete locally proved negative answer to the entire canonical direct induced-norm uniqueness conjecture, with all eight exports approved by two independent statement and two independent final proof referees. The exact p=4 matrices are two distinct global minimizers over all complex right inverses. Actual Linux sandboxed Comparator/default-kernel execution, controls, independent operational audit and publication review remain pending. Canonical status remains Solved.',
   'sorry_count':0,'sorry_in_definitions':0,'axioms':axioms,
   'main_results':[{'declaration':name,'file':'Solution.lean','sorry_count':0,'axioms':axioms.copy(),'comparator_config':'comparator.json','literature_dependencies':[]} for name in config['theorem_names']]},
 'fidelity':{'divergences':'No narrowing of the original conjecture being negated. The same source matrices at m=2,n=3,p=4 suffice to refute its all-dimension/all-p statement. Generic denominator/supremum semantics are proved on every original domain. The actual complex inverse, rank, Euclidean norm, real powers, all-input suprema and all-right-inverse global minimality are retained. The stronger source all-p formulas and full minimizer classifications, higher-dimensional families, smallest-dimension classification, endpoints and separate product objective are outside these exports.'},
 'review':{'status':'agent-reviewed; actual Linux Comparator/default-kernel verification pending',
   'reviewers':['OpenAI Codex agent /root/solved_statement_inventory: independent statement referee 1 and final proof referee 1',
                'OpenAI Codex agent /root: independent statement referee 2 and final proof referee 2'],
   'notes':'Both statement approvals preceded proof implementation and include the unchanged additive Comparator supplement. Both final referees freshly elaborated ten commands in private prefixes excluding old IE-23 objects and inspected actual proof terms. Each traversed 93 project declarations; referee 1 checked 40 retained dependencies and referee 2 checked 28, adding twelve kernel assertions. All sixteen internal/public transitive axiom reports contain exactly propext, Classical.choice and Quot.sound. LeanCert supplies explicit kernel trust auditing only; there is no numerical interval certificate. Challenge placeholders remain isolated. All local checks used Lean 4.33.1 on macOS with clean exact pinned MI-22 dependency objects reused read-only; there was no local Lake invocation, full dependency-source rebuild or Linux run. Packaging archives and refreshes only the historical README among 104 proof-freeze inputs, preserving all other 103 inputs, original eight sources/snapshots, all review evidence and the configuration supplement. The source plan, proof map and earlier phase labels remain historical. Actual Linux verification and operational/publication reviews are pending.',
   'statement_reports':[{'file':p,'sha256':h} for p,h in report_hashes.items() if '/statement-' in p],
   'proof_reports':[{'file':p,'sha256':h} for p,h in report_hashes.items() if '/proof-' in p],
   'proof_freeze':{'file':'reviews/proof-freeze.json','sha256':sha(proof_freeze)},
   'configuration_supplement':{'file':'reviews/statement-config-supplement.json','sha256':'dafd6645aa017c543dd4eb9f60633b47a2035f090d58955525a3d6c41156141a'},
   'proof_report_evidence':{p:{'sha256':h,'bytes':(project/p).stat().st_size} for p,h in evidence_hashes.items() if '/proof-' in p},
   'linux_verification':{'status':'pending','note':'No IE-23 project-specific Linux run, Comparator success, default-kernel replay or operational approval is claimed. Shared infrastructure success does not verify this problem.'}},
 'alignment':[{'declaration':name,'scope':scope} for name,scope in zip(config['theorem_names'],scopes)],
 'acknowledgements':'Matthew J. Colbrook for the mathematical resolution; Dokmanić and Gribonval for the underlying example and original question; Mathlib and LeanCert contributors for actual norms, powers, matrix rank/inverse, supremum and kernel-trust APIs. Shared Comparator/exporter/sandbox tools retain their licenses and attribution. No external mathematical theorem is an unproved premise.'
}
(project/'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+yaml.safe_dump(manifest,sort_keys=False,allow_unicode=True,width=100))
(candidate/'prepare.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'result':'Candidate metadata written; Linux remains pending','preexisting_project_inputs':len(inputs),'proof_frozen_inputs':len(freeze['files']),
                  'exports':len(config['theorem_names']),'README_sha256':sha(project/'README.md'),'formalization_sha256':sha(project/'formalization.yaml')},indent=2))
