"""Package accepted MF12 math bytes; only documentation/configuration changes.
No Lean/Lake execution, Git mutation, workflow dispatch or status promotion.
"""
from pathlib import Path
import hashlib, json, re, shutil, subprocess
import yaml

root=Path('/tmp/nla-lean-next-20260915')
source=root/'matrix-functions/MF-12'
project=root/'MF12-canonical-package'
run=root/'development-runs/35034380090'
review=root/'reviews/MF12-elimination-complete-source/development35034380090-addendum'
repo=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
upstream='ce47b5630bf3680d9211131c3a43825b022c139a'
sha=lambda b:hashlib.sha256(b).hexdigest()
audit=json.loads((review/'CHECKS.json').read_text())
assert audit['whole_problem_verified'] is False
assert audit['all28_kernel_trust_assertions_accepted']
assert not project.exists(), project
project.mkdir()

# Retain exactly the mathematical source which actually compiled.
for rel in audit['all19_reviewed_solution_closure_bytes_unchanged']:
    src=source/rel;dst=project/rel;dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(src,dst)
for name in ['Challenge.lean','LICENSE','NUMERICAL_TARGETS.md','SOURCE-PROVENANCE.json',
             'STATEMENT-FREEZE.json','comparator.json','lake-manifest.json','lakefile.toml','lean-toolchain']:
    shutil.copyfile(source/name,project/name)
shutil.copytree(source/'statement-audit',project/'statement-audit')
shutil.copytree(source/'source',project/'source')

pack=project/'verification/packaging';before=pack/'before';before.mkdir(parents=True)
for f in source.iterdir():
    if f.is_file() and (f.suffix in ['.json','.yaml','.md','.toml']):
        shutil.copyfile(f,before/f.name)
shutil.copyfile(Path(__file__),pack/'prepare_mf12_canonical_package.py')

# All reports and snapshots preserve bytes. Historical Lean source copies get a
# .txt suffix outside active source; the exact original-to-retained path map is kept.
pathmap=[]
def retain_tree(original,destination):
    for old in sorted(original.rglob('*')):
        if not old.is_file():continue
        rel=old.relative_to(original)
        if old.suffix=='.lean':rel=Path(str(rel)+'.txt')
        new=destination/rel;new.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(old,new)
        pathmap.append({'original_path':str(old),'retained_path':str(new.relative_to(project)),
                        'sha256':sha(old.read_bytes()),'content_unchanged':True})
for name in ['MF12-elimination-proof-prefix','MF12-elimination-next-prefix',
             'MF12-elimination-lower-prefix','MF12-elimination-complete-source']:
    retain_tree(root/'reviews'/name,project/'reviews/proof-source'/name)
# Two actual independent statement reports are preserved at their freeze-recorded
# paths above; these copies provide their complete read-only supporting evidence.
for name in ['MF12-root-statements','MF12-elimination-statements']:
    retain_tree(root/'reviews'/name,project/'reviews/statement-source'/name)
retain_tree(source/'compile-history',project/'reviews/implementation-history')
(pack/'REVIEW-PATH-MAP.json').write_text(json.dumps(pathmap,indent=2)+'\n')

evidence=project/'verification/development-35034380090'
shutil.copytree(run,evidence)

lake=project/'lakefile.toml';old_lake=lake.read_bytes()
assert old_lake.count(b'defaultTargets = ["Challenge"]')==1
lake.write_bytes(old_lake.replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]'))
assert 'name = "Solution"' in lake.read_text()

metadata=yaml.safe_load((source/'formalization.yaml').read_text())
metadata['project']['description']=('Complete compiled proof candidate for every nonnegative real polynomial growth exponent '
    'using a fixed positive-dimensional real matrix pair, all words at every positive length, '
    'genuine Euclidean operator norm and the actual nth-root limit one.')
metadata['repository']['note']=('The exact proof graph compiled at a1efcbfc59263b9e5bb00914ee709112348c1e54 '
    'in Linux development run 35034380090. This standalone candidate awaits its canonical check.')
metadata['automation']['methods'][0]['tool_setup']=('Definitions and all 28 Challenge signatures were independently reviewed by two agents '
    'and actually elaborated on Linux before an immutable freeze and any proof bodies. '
    'Source drafting occurred on macOS; non-root Linux development compiled the full proof graph. '
    'No local Lean/Lake execution or dependency/cache download was performed by the proof/referee agents.')
metadata['automation']['methods'][0]['prompting_notes']=('Retain all words, every positive length, every nonnegative real exponent, '
    'actual attained maxima, genuine Euclidean norms and actual nth-root convergence. '
    'Sparse block algebra, finite Holder, rational Bernoulli constants and fixed dimension-factor '
    'norm comparisons avoid interval subdivisions. Every export uses LeanCert kernel trust; '
    'standalone Comparator and default-kernel replay remain pending.')
metadata['automation']['notes']=('Substantial AI assistance. Proof implementation by OpenAI Codex agent /root/next_matrix_functions '
    'for George Stepaniants. Independent source and development-evidence review by /root/next_elimination; '
    'that agent also prepared this metadata/configuration package but changed no mathematical source. '
    'Two prior statement reviewers were /root and /root/next_elimination. A second independent complete '
    'mathematical reviewer and all canonical operational gates are still pending. '
    'No official Tau Ceti endorsement, external human peer review or source-author endorsement is claimed.')
config=json.loads((project/'comparator.json').read_text())
names=config['theorem_names'];assert len(names)==28
results=[]
for name in names:
    file=audit['all28_source_locations'][name]
    results.append({'declaration':name,'file':file,'sorry_count':0,
        'axioms':audit['all28_observed_axioms'][name],'comparator_config':'comparator.json',
        'literature_dependencies':[],
        'verification_status':'Actual complete Linux development compilation and LeanCert kernel-trust assertion passed; standalone canonical acceptance pending.'})
metadata['status']={'scope':('All 28 frozen targets and their complete 19-file Solution closure passed actual non-root Linux '
    'development compilation in successful run 35034380090, including the complete every-real-exponent theorem. '
    'All observed transitive axioms are standard. The 28 deliberate independent Challenge placeholders are '
    'specifications and excluded from proof-development sorry counts. Standalone Comparator, independent '
    'default-kernel replay, rejection controls and two final independent referee verdicts remain pending. '
    'The canonical original status is not changed by this package.'),
    'sorry_count':0,'sorry_in_definitions':0,'axioms':['propext','Classical.choice','Quot.sound'],
    'main_results':results,'whole_problem_verified':False}
metadata['fidelity']['divergences']=('The unchanged six-dimensional source pair uses lambda=1/4. For 0<alpha<1, '
    'the proved sufficient constants are c=lambda^alpha/10 and C=1728/(1-mu)^2. Exact Bernoulli estimates '
    'replace exponential constants, and entry-max comparisons replace spectral-norm Kronecker '
    'multiplicativity with proved fixed dimension factors. These change constants only and preserve '
    'every positive length, real exponent, true norm, actual family maximum and root limit. '
    'No optional rational-entry, density, sharper-constant or minimal-dimension corollary is claimed.')
metadata['review']={'status':'two independent statement approvals and one independent complete mathematical-source/development acceptance; second full referee and canonical final gates pending',
    'reviewers':['/root (independent statement referee)',
                 '/root/next_elimination (independent statement and mathematical-source/evidence referee; metadata packager only)'],
    'notes':('Original statement approvals, actual pre-proof declaration receipt and immutable freeze are retained. '
        'The complete full-source review chain and all source-repair addenda are retained with exact hashes. '
        'The development acceptance addendum independently binds all 120 shared-run Git inputs, all command '
        'and archive hashes, all 19 Solution closure files and actual 28 export results. '
        'Final acceptance still requires a second non-implementing full mathematical review and two '
        'non-implementing operational source/evidence verdicts for canonical Comparator, default-kernel '
        'replay and rejection controls under the scoped Tau Ceti protocol.')}
metadata['alignment']['implemented_entry']='Solution.lean'
metadata['alignment']['active_source_manifest']='ACTIVE-SOURCE-MANIFEST.json'
metadata['toolchain']={'lean':'leanprover/lean4:v4.33.1','dependency_manifest':'lake-manifest.json',
    'dependencies':{'leancert':'621a43d7cf21f87872392a01e874f2f1dbddc926','mathlib':'0df444a360eaa60ab8c11dca51a86af692955474'}}
metadata['verification']={'development_run':'https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35034380090/job/104599995558',
    'development_commit':'a1efcbfc59263b9e5bb00914ee709112348c1e54',
    'complete_development_build':'passed','leancert_kernel_trust_assertions':'passed for all 28 frozen exports',
    'observed_axioms':'Per-declaration standard axiom sets recorded in status.main_results and the independent evidence addendum.',
    'statement_elaboration':'passed before proof implementation in run 35026411039; immutable freeze and actual receipt retained',
    'comparator':'pending','default_kernel':'pending','negative_controls':'pending',
    'permitted_axioms':['propext','Classical.choice','Quot.sound']}
(project/'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'+
    yaml.safe_dump(metadata,sort_keys=False,allow_unicode=True,width=100))

(project/'README.md').write_text('''# MF-12 Lean formalization

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. Original mathematical proof: Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
No contact email is included.

**The complete proof graph has compiled; standalone canonical verification is
pending.** All 28 frozen targets passed actual non-root Linux development
[run 35034380090](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35034380090/job/104599995558)
at revision `a1efcbfc59263b9e5bb00914ee709112348c1e54`. This package preserves
all 19 mathematical source files in that accepted Solution closure. Every final
export passed its LeanCert kernel-trust assertion and reported only standard
axioms; the exact per-declaration sets are retained in `formalization.yaml`.

The full conclusion covers every nonnegative real exponent gamma. A fixed
positive dimension and exactly two distinct fixed real matrices have maximal
norms of all length-n products between fixed positive multiples of n^gamma for
every positive integer n. The norm is the genuine Euclidean operator norm, the
maximum ranges over the complete family-word set and is actually attained, and
the actual nth-root sequence converges to one. The dimension and matrices depend
on gamma, never on the product length.

The proof uses the source's explicit six-dimensional fractional pair and an
ordinary Jordan block for integer exponents. Sparse block identities, finite
Holder, exact rational Bernoulli bounds, integer logarithms and fixed
dimension-factor tensor comparisons avoid interval subdivision and approximate
spectral computations. The sufficient constants are deliberately enlarged;
optional source claims about rational entries, density, sharper constants and
minimal dimension are outside this verification scope.

With the pinned toolchain available, from this directory:

```bash
lake exe cache get
lake build +Solution
```

The default `lake build` also selects Solution. Changing the earlier statement
phase's default target is a configuration transition; it changes no mathematical
source or dependency revision. No local Lean/Lake build or cache download was
performed in preparing this package. A build alone does not replace the stronger
[canonical verification protocol](../../../docs/lean/README.md).

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md),
[Definitions.lean](NLA/MF12/Definitions.lean), and
[Challenge.lean](Challenge.lean) for the complete frozen specification.
Challenge's 28 deliberate placeholders are independently trusted statements and
are never imported by [Solution.lean](Solution.lean). Two independent statement
approvals and actual Linux elaboration preceded proof construction; the
[freeze](STATEMENT-FREEZE.json) and [original records](statement-audit) preserve
that boundary. Their historical draft descriptions remain part of the evidence.

The [complete mathematical source review](reviews/proof-source/MF12-elimination-complete-source/REVIEW.md)
and [actual development acceptance addendum](reviews/proof-source/MF12-elimination-complete-source/development35034380090-addendum/REVIEW.md)
retain their exact original bytes alongside earlier reviews and repairs.
The reviewer also prepared this metadata package without modifying proof code.
A second independent full mathematical reviewer is still required. The reviews
are AI-agent reviews under scoped Tau Ceti criteria, not external human review
or official certification.

[SourceCorrespondence.md](SourceCorrespondence.md) maps every declaration to the
full original target and proof. [formalization.yaml](formalization.yaml) records
all 28 exports and current status. [ACTIVE-SOURCE-MANIFEST.json](ACTIVE-SOURCE-MANIFEST.json)
binds the compiled mathematical bytes; [development evidence](verification/development-35034380090)
and the [packaging transition](verification/packaging) distinguish the tested
shared development revision from this standalone candidate.

Actual standalone Comparator, independent default-kernel replay, required
negative controls and two final source/evidence referee verdicts remain pending.
This package does not change the canonical problem status or any index.
''')

correspondence=(source/'SourceCorrespondence.md').read_text()
correspondence=correspondence.replace('Status: proof-free statement package. No independent approval or Lean execution\nis claimed. Every entry below is a proposed Challenge obligation, not a result.',
    'Status: the complete reviewed proof graph passed actual Linux development run\n35034380090 at a1efcbfc59263b9e5bb00914ee709112348c1e54. Standalone canonical\nverification remains pending. Every entry below is implemented at the unchanged\nfrozen Challenge signature; the original draft is preserved in statement-audit.')
correspondence=correspondence.replace('| Proposed declarations |','| Implemented declarations |')
old_end='''Definitions and all28 proposed signatures require two independent source
reviews and actual remote Linux elaboration before an immutable freeze and any
proof implementation. Comparator must compare all28 exports without replaceable
definition holes; final acceptance also requires all LeanCert kernel assertions,
standard-axiom reports, default-kernel replay, negative controls and two final
independent referees. This package claims no completed verification.
'''
assert old_end in correspondence
correspondence=correspondence.replace(old_end,'''Definitions and all 28 independent signatures were reviewed by two independent
agents and actually elaborated on non-root Linux in run 35026411039 before the
immutable freeze and any proof implementation. The exact originals, statement
reviews, source provenance and pre-proof receipt remain in statement-audit/.

All 19 Solution closure files now match the actual successful development inputs
at a1efcbfc59263b9e5bb00914ee709112348c1e54. Every target passed its LeanCert
kernel-trust assertion. The exact observed axiom set for gap_decomposition is
propext/Quot.sound; the other 27 use the standard three. All 28 textual types
match the frozen Challenge, and the Solution closure contains no holes, custom
axioms or Challenge import. The full source review chain, proof-only repair
addenda and independent actual-log reconciliation are retained under reviews/.

Preparing this standalone package changes only metadata, source-correspondence
status text and the default Lake target from Challenge to Solution. The exact
before versions are retained under verification/packaging/before/. It does not
change any mathematical definition, signature, proof byte or dependency pin.
The packaging reviewer contributed no mathematical implementation.

Standalone Comparator must still compare all 28 exports without replaceable
definition holes; independent default-kernel replay and negative controls are
also pending. A second independent full mathematical review and two final
source/evidence referee verdicts remain necessary. Complete development
compilation is not a claim that these canonical gates have already run.
''')
(project/'SourceCorrespondence.md').write_text(correspondence)

(pack/'README.md').write_text('''# Standalone packaging record

This is a metadata/configuration/evidence-only copy of the MF-12 proof files
accepted in development run 35034380090. `before/` preserves original top-level
metadata and configuration; `statement-audit/` preserves the immutable earlier
statement boundary. `TRANSITION.json` records every intentional top-level change.
No mathematical Lean file, numerical statement or dependency pin changed.

The original proof-review chain and author repair history are copied with exact
bytes. Historical `.lean` copies outside active source use the `.lean.txt` suffix;
`REVIEW-PATH-MAP.json` binds each original path, retained path and content hash.
These are evidence snapshots, never imported proof modules.

The package was prepared by the independent mathematical reviewer as a separate
clerical contribution. Its full source approval precedes packaging and changes
no proof. Whole-problem verified status remains false until actual canonical
Comparator, independent kernel replay, rejection controls and two final referee
verdicts. No Git mutation, push, workflow dispatch or canonical status promotion
is part of this preparation.
''')

# Bind the unchanged original mathematical inputs and the explicitly changed docs.
active=dict(audit['all19_reviewed_solution_closure_bytes_unchanged'])
active['Challenge.lean']=sha((project/'Challenge.lean').read_bytes())
active['NUMERICAL_TARGETS.md']=sha((project/'NUMERICAL_TARGETS.md').read_bytes())
for rel,digest in active.items():assert sha((project/rel).read_bytes())==digest,rel
(project/'ACTIVE-SOURCE-MANIFEST.json').write_text(json.dumps({'scope':'Exact accepted mathematical source and frozen boundary; no canonical-verification claim.',
    'accepted_development_commit':audit['actual_commit'],'accepted_development_run':audit['actual_run'],
    'mathematical_files_sha256':active,'all19_solution_closure_bytes_equal_accepted_inputs':True,
    'statement_freeze_sha256':sha((project/'STATEMENT-FREEZE.json').read_bytes()),
    'comparator_config_sha256':sha((project/'comparator.json').read_bytes()),
    'canonical_verification':'pending','whole_problem_verified':False},indent=2)+'\n')
changes={}
for name in ['README.md','SourceCorrespondence.md','formalization.yaml','lakefile.toml']:
    changes[name]={'before_sha256':sha((source/name).read_bytes()),'after_sha256':sha((project/name).read_bytes()),
                  'before_path':'verification/packaging/before/'+name}
(pack/'TRANSITION.json').write_text(json.dumps({'kind':'standalone candidate metadata/configuration/evidence preparation',
    'packager':'OpenAI Codex agent /root/next_elimination','accepted_development_commit':audit['actual_commit'],
    'accepted_development_run':audit['actual_run'],'intended_upstream_base':upstream,
    'canonical_problem_path':'matrix-functions-and-stability/MF-12/README.md',
    'mathematical_files_unchanged':active,'changed_top_level_files':changes,
    'default_target_change':'Challenge -> Solution','dependency_revisions_unchanged':True,
    'original_statement_freeze_unchanged':True,'proof_implementation_changes':False,
    'canonical_comparator':'pending','whole_problem_verified':False},indent=2)+'\n')

# Copy the exact latest upstream schema validator as evidence, then run only that
# small Python metadata check using the pre-existing Python environment.
gov=pack/'upstream-validator';gov_sources={}
for rel in ['tools/lean/validate_manifest.py','docs/lean/schema/v0.4.schema.json']:
    b=subprocess.check_output(['git','show',upstream+':'+rel],cwd=repo)
    f=gov/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
    gov_sources[rel]=sha(b)
(gov/'SOURCE.json').write_text(json.dumps({'upstream_commit':upstream,'files':gov_sources},indent=2)+'\n')
print(json.dumps({'project':str(project),'unchanged_solution_closure_files':19,'frozen_challenge_goals':28,
    'copied_review_evidence_files':len(pathmap),'canonical_verification':'pending'},indent=2))
