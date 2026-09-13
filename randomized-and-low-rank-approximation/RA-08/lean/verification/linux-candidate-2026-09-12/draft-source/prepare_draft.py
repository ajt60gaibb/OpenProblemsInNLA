"""Prepare an external-only RA-08 metadata candidate after final proof review.

Reads the actual MF-16 candidate layout and RA-08 frozen sources. Never changes
the worktree, archives, proofs, pins, metadata or status. The tiny external
validation overlay exists solely for the official metadata/file validator;
no Lean command is run.
"""
from pathlib import Path
import datetime, difflib, hashlib, importlib.util, json, re, shutil, subprocess
import yaml

D = Path(__file__).resolve().parent
P = Path('/tmp/nla-lean-ra08-worktree/randomized-and-low-rank-approximation/RA-08/lean')
W = P.parents[2]
M = Path('/tmp/nla-lean-mf16-worktree/matrix-functions-and-stability/MF-16/lean')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
old_readme = '1b6b1796019062b3bc983b380a410fa3d52f07f9e1f3e5120bd0d1fc8257f9c5'
old_metadata = '9ca52885b2ebfd85c2d4eba626d290fb93c2fff47287c2aff490123771be9c52'
assert sha(P/'README.md') == old_readme
assert sha(P/'formalization.yaml') == old_metadata
acceptance = 'verification/final-review-acceptance.json'
assert sha(P/acceptance) == 'ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d'
assert json.loads((P/acceptance).read_text())['gate'].startswith('ACCEPT both independent final mathematical approvals')
pf = json.loads((P/'verification/proof-freeze.json').read_text())
sf = json.loads((P/'reviews/statement-freeze.json').read_text())
assert len(pf['files']) == 450 and len(sf['files']) == 39
for f in (pf, sf):
    assert 'README.md' in f['files'] and 'formalization.yaml' in f['files']
    for rel, h in f['files'].items():
        assert sha(P/rel) == h, rel
    for rel, h in f['source_files'].items():
        raw = subprocess.check_output(['git','-C',str(W),'show',f['base']+':'+rel])
        assert hashlib.sha256(raw).hexdigest() == h and (W/rel).read_bytes() == raw
assert not (P/'verification/pre-candidate-README.md').exists()
assert not (P/'verification/pre-candidate-formalization.yaml').exists()
meta = yaml.safe_load((P/'formalization.yaml').read_text())
config = json.loads((P/'comparator.json').read_text())
names = config['theorem_names']
assert len(names) == len(set(names)) == 14 and config['definition_names'] == []
axioms = ['propext','Classical.choice','Quot.sound']
assert config['permitted_axioms'] == axioms
scopes = [
    'Every actual real PSD matrix admits complete ordered orthogonal spectral data, including repeated eigenvalues and zero dimension.',
    'The selected columns are actual orthonormal eigenvectors, the selected eigenvalue combination reconstructs the matrix, and actual positive semidefiniteness follows.',
    'For every selected ordered spectral decomposition and every real scalar function, genuine CFC equals the selected spectral combination and is independent of the extension outside the nonnegative half-line.',
    'For every selected basis and admissible function, the actual Euclidean operator-norm tails of the original and function truncations equal the first discarded eigenvalue and its function value.',
    'For every real matrix and real vector, the absolute quadratic form is at most the genuine Euclidean operator norm times the squared Euclidean vector norm.',
    'The unchanged source function and rational matrices satisfy admissibility, the exact projection and complement identities, positive definiteness and actual PSD order.',
    'The actual real spectrum of the fixed witness is contained in [0,1] union [17/16,infinity); the entire open spectral gap is excluded by proof.',
    'The exact scalar polynomial minorant lies below min(x,1) throughout the entire proved nonnegative unbounded spectral set, with no operator-monotonicity assertion.',
    'The actual polynomial CFC of the witness equals the stated matrix polynomial, which is below the genuine kink-function CFC in actual PSD order.',
    'For every permitted witness eigendecomposition, the residual norm and fourth eigenvalue are exactly t and the actual approximation truncations and both optimal tails have the stated values.',
    'All exact vector, matrix-product, squared-length, approximation CFC and actual minorant Rayleigh identities hold, with Rayleigh value 26*t*(1+witnessGap).',
    'The actual rational witnessGap is strictly positive, using the explicit-kernel LeanCert strict-upper-bound checker for zero on the singleton [0,0]; this term is materially used by the final result.',
    'For every allowed ordered decomposition of the actual admissible source pair, the original spectral inequality holds at error zero and the transformed spectral inequality fails.',
    'Unconditional negation of the complete canonical universal implication, retaining every original real PSD pair, dimension, rank, function, nonnegative error parameter and selected eigenbasis.'
]
assert len(scopes) == len(names)
meta['project']['name'] = 'RA-08: an exact concave spectral-transfer counterexample'
meta['project']['description'] = ('Complete negative answer to the original real PSD concave spectral-transfer implication, '
    'using Colbrook\'s unchanged six-dimensional rational witness, genuine CFC and Euclidean operator norms, '
    'and an exact polynomial minorant.')
meta['sources'][1]['title'] = 'Concave matrix-function error transfer can fail for exact Nyström approximations'
meta['sources'][1]['location'] = 'Theorem 3.1 and its complete proof; SourceCorrespondence.md and PROOF_MAP.md map the unchanged witness and adapted proof route'
meta['sources'][1]['note'] = ('Colbrook retains mathematical authorship. The source witness at t=1/65536 is unchanged. '
    'The exact polynomial route proves a weaker strictly positive rational margin than the contour bound, sufficient '
    'for the complete canonical negative answer. The larger contour ratio, separate Nyström sketch identity and '
    'ancillary nuclear or stronger extensions are outside the fourteen exports.')
meta['automation']['methods'][0]['tool_setup'] = ('Multiple implementation agents; two frozen statement approvals before '
    'implementation, then two independent final mathematical reviews with fresh private-prefix source compilation and '
    'actual type-and-body dependency inspection. Authoritative Linux and publication gates remain separate.')
meta['automation']['methods'][0]['prompting_notes'] = ('Preserve every original real PSD, function, parameter and eigenbasis '
    'quantifier. Prove actual spectral and selected CFC semantics. Minimize computation with exact compression and '
    'finite-dimensional kernels, a same-matrix polynomial CFC minorant, three unnormalized rational matrix-vector '
    'products and one materially consumed explicit-kernel LeanCert singleton strict-gap certificate. Do not assume '
    'numerical eigenvalues, tail identities or operator monotonicity of min(x,1).')
meta['automation']['notes'] = ('AI-assisted formalization requested by George Stepaniants. Main implementation and selected '
    'CFC identification: /root/formal_review_standards. Generic spectral/norm lemmas and disclosed compression route: '
    '/root. Ordered spectral existence: /root/solved_statement_inventory. The latter two previously reviewed the '
    'frozen statements but later became implementation coauthors; none of these three is an independent final '
    'mathematical referee. Final referees are /root/leancert_examples and /root/mf16_final_referee. No human peer '
    'review, official Tau Ceti endorsement, source-author endorsement, measured cost or new priority is claimed.')
meta['status'] = {
    'scope': ('Complete fourteen-export proof of the negative answer to the full original all-real-PSD, all-function, '
        'all-parameter and all-selected-eigenbasis concave spectral-transfer implication. Two frozen statement '
        'approvals preceded implementation and two independent final mathematical reports approving the complete '
        'proof have been accepted. Actual Ubuntu Comparator/default-kernel and real-control execution, independent operational '
        'acceptance and publication review remain pending. Canonical status remains Solved.'),
    'sorry_count': 0, 'sorry_in_definitions': 0, 'axioms': axioms,
    'main_results': [{'declaration':n,'file':'Solution.lean','sorry_count':0,'axioms':axioms,
                     'comparator_config':'comparator.json','literature_dependencies':[]} for n in names]
}
meta['fidelity']['divergences'] = ('No narrowing of the original universal implication being refuted. Every real '
    'dimension, rank, nonnegative error parameter, continuous nonnegative nondecreasing concave half-line function '
    'and selected ordered orthogonal eigenbasis is retained. Generic f(0)=0 is not assumed. Actual CFC, PSD order, '
    'Euclidean operator norm and every-basis truncation semantics are proved. The unchanged source witness is '
    'handled by an exact polynomial minorant with a weaker sufficient strict margin; the source larger contour '
    'ratio, separate Nyström sketch identity and ancillary stronger extensions are not exported.')
entry = lambda n: {'file':n,'sha256':sha(P/n)}
manifests = ['reviews/final-referee-1-evidence/EVIDENCE-MANIFEST.json',
             'reviews/final-referee-2-evidence/EVIDENCE-MANIFEST.json']
statement_manifests = ['reviews/statement-referee-1-evidence/EVIDENCE-MANIFEST.json',
                       'reviews/statement-referee-2-evidence/EVIDENCE-MANIFEST.json']
meta['review'] = {
    'status': 'agent-reviewed; actual Linux Comparator and default-kernel verification pending',
    'reviewers': [
        'OpenAI Codex agent /root/solved_statement_inventory: historical independent statement referee 1, later ordered-spectral-existence coauthor',
        'OpenAI Codex agent /root: historical statement referee 2 and disclosed compression-route contributor, later generic spectral/norm coauthor; not an independent final mathematical referee',
        'OpenAI Codex agent /root/leancert_examples: independent final mathematical referee 1',
        'OpenAI Codex agent /root/mf16_final_referee: independent final mathematical referee 2'],
    'notes': ('Both statement approvals preceded implementation. Both independent final referees read the complete '
        'original source and actual definitions, all sixteen mathematical modules and all fourteen exports; freshly '
        'compiled candidate sources and independent inspectors in private macOS prefixes; and independently '
        'reconstructed the exact projection, positive-definiteness/compression certificates, polynomial products '
        'and strict rational gap. Referee 1 records twenty successful commands and 61 standard-three axiom reports; '
        'referee 2 records nineteen and 62. Their actual type-and-body traversals independently reach 215 project '
        'declarations from the full negation and retain the material numerical helper and genuine CFC/norm/spectral '
        'chain; differing selected dependency sets are documented in their reports. Only the ten exact clean pinned '
        'MI-22 dependency sources/objects were reused read-only, with old project objects excluded and no Lake or '
        'dependency rebuild. Reviewer-only tool/display corrections and failed development attempts are retained. '
        'No mathematical correction was requested. Candidate packaging replaces only README.md and formalization.yaml '
        'among frozen proof and statement inputs, retaining both exact originals at the named pre-candidate archives. '
        'The other 448 proof inputs, 37 statement inputs and all ten original Git sources remain unchanged. The '
        'retained numerical term checks constant zero on [0,0] strictly below the exact positive gap with the actual '
        'LeanCert strict-upper-bound checker, then feeds the complete negation. Actual Ubuntu Comparator, '
        'default-kernel replay, both real control suites, independent operational and publication acceptance remain '
        'required. No local check is reported as Linux or official Comparator execution.'),
    'statement_freeze': entry('reviews/statement-freeze.json'),
    'proof_freeze': entry('verification/proof-freeze.json'),
    'statement_reports': [entry('reviews/statement-referee-1.md'),entry('reviews/statement-referee-2.md')],
    'proof_reports': [entry('reviews/final-referee-1.md'),entry('reviews/final-referee-2.md')],
    'proof_report_evidence': {n:{'sha256':sha(P/n),'bytes':(P/n).stat().st_size} for n in manifests},
    'statement_report_evidence': {n:{'sha256':sha(P/n),'bytes':(P/n).stat().st_size} for n in statement_manifests},
    'coordinator_acceptance': entry(acceptance),
    'linux_verification': {'status':'pending',
        'note':'A new actual Ubuntu branch run, all fourteen Comparator exports, default-kernel replay and both real control suites are required before publication-status promotion.'},
    'historical_readme': {'file':'verification/pre-candidate-README.md','sha256':old_readme},
    'historical_formalization': {'file':'verification/pre-candidate-formalization.yaml','sha256':old_metadata},
}
meta['alignment'] = [{'declaration':n,'file':'Solution.lean','scope':s} for n,s in zip(names,scopes)]
meta['acknowledgements'] = ('Matthew J. Colbrook for the mathematical counterexample; Persson, Meyer and Musco for '
    'the original question. Mathlib and LeanCert contributors for genuine spectral theorem, selected CFC, PSD '
    'order, Euclidean operator norm, dimension and kernel-checker APIs. The selected CFC architecture credits '
    'its actual Mathlib source. Shared checker/exporter/sandbox tools, all source licenses and original '
    'attributions are retained.')
header = '# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n'
(D/'formalization.yaml').write_text(header+yaml.safe_dump(meta,sort_keys=False,allow_unicode=True,width=104))

archive_plan = {
    'status':'External checked draft; parent accepted both final reviews and authorized archive/live installation after this draft passes schema and coverage.',
    'project':str(P),'canonical_status':'Solved, unchanged',
    'live_changes_allowed_after_authorization':['README.md','formalization.yaml'],
    'archives_required_before_any_live_replacement':[
        {'source':'README.md','archive':'verification/pre-candidate-README.md','sha256':old_readme},
        {'source':'formalization.yaml','archive':'verification/pre-candidate-formalization.yaml','sha256':old_metadata}],
    'ordered_install_plan':[
        'Read and bind root final-review acceptance ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d and the explicit archive/install parent authorization before any live change.',
        'Recheck all original 450 proof, 39 statement and ten source identities before any replacement.',
        'Create both archive files from the exact live historical bytes; require absence or identical content, never overwrite a different archive.',
        'Verify both archive hashes, then replace only live README.md and formalization.yaml with the parent-reviewed draft bytes.',
        'Recheck all 448 other proof inputs, 37 other statement inputs, every ten-source immutable Git identity, and all review/evidence inventories.',
        'Run actual installed v0.4 schema and complete fourteen-export metadata coverage checks; no Lean, pin, comparator or canonical change.',
        'Bind exact candidate tracked-input inventory and blank-email commit in the separate authorized root candidate stage.',
        'Only an actual successful Ubuntu run and subsequent operational/publication acceptance may permit canonical promotion.'
    ],
    'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),
    'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
    'draft_readme_sha256':sha(D/'README.md'), 'draft_metadata_sha256':sha(D/'formalization.yaml'),
    'two_final_reports':meta['review']['proof_reports'],
    'two_final_inventories':meta['review']['proof_report_evidence'],
    'coordinator_acceptance':entry(acceptance),
    'no_live_changes_performed':True,
}
(D/'ARCHIVE-AND-INSTALL-PLAN.json').write_text(json.dumps(archive_plan,indent=2)+'\n')
for n in ('README.md','formalization.yaml'):
    diff=''.join(difflib.unified_diff((P/n).read_text().splitlines(True),(D/n).read_text().splitlines(True),
                                     fromfile='historical/'+n,tofile='candidate/'+n))
    (D/(n+'.diff')).write_text(diff)

# Use exact small source/config copies to exercise the repository metadata
# validator externally. This neither imports nor elaborates Lean.
V=D/'validation-overlay';V.mkdir(exist_ok=True)
for n,src in [('formalization.yaml',D/'formalization.yaml'),('comparator.json',P/'comparator.json'),
              ('Solution.lean',P/'Solution.lean')]:
    (V/n).write_bytes(src.read_bytes())
validator_path=W/'tools/lean/validate_manifest.py'
spec=importlib.util.spec_from_file_location('nla_manifest_validator',validator_path)
validator=importlib.util.module_from_spec(spec);spec.loader.exec_module(validator)
schema_path=W/'docs/lean/schema/v0.4.schema.json'
validator.validate(V,json.loads(schema_path.read_text()))

# Validate links as they will resolve in the intended project, allowing only
# the two deliberately future archives from the reviewed install plan.
planned={x['archive'] for x in archive_plan['archives_required_before_any_live_replacement']}
links=[]
for target in re.findall(r'\]\(([^)]+)\)',(D/'README.md').read_text()):
    assert '://' not in target
    assert (P/target).exists() or target in planned,target
    links.append({'target':target,'exists_live':(P/target).exists(),'planned_archive':target in planned})
assert '@' not in (D/'README.md').read_text() and '@' not in (D/'formalization.yaml').read_text()
for f in (pf,sf):
    for rel,h in f['files'].items():assert sha(P/rel)==h,rel
assert not subprocess.check_output(['git','-C',str(W),'diff','--name-only'])
assert not subprocess.check_output(['git','-C',str(W),'diff','--cached','--name-only'])
inputs=[P/'README.md',P/'formalization.yaml',P/'Solution.lean',P/'comparator.json',
        P/'reviews/proof-completion.md',P/'verification/implementation-roles.json',P/acceptance,
        P/'verification/proof-freeze.json',P/'reviews/statement-freeze.json',
        P/'reviews/statement-referee-1.md',P/'reviews/statement-referee-2.md',
        P/'reviews/final-referee-1.md',P/'reviews/final-referee-2.md',
        *(P/n for n in manifests+statement_manifests),M/'README.md',M/'formalization.yaml',validator_path,schema_path,
        W/'randomized-and-low-rank-approximation/RA-08/README.md',
        W/'references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.tex']
record={
    'verdict':'PASS external-only candidate metadata schema, fourteen-export coverage, link and source-preservation checks',
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'preparer':'/root/leancert_examples; RA08 independent final referee 1 now performing a separate documentation-preparation role',
    'live_proof_inputs_unchanged':450,'live_statement_inputs_unchanged':39,'original_sources_unchanged':10,
    'all_inputs':{str(p):{'sha256':sha(p),'bytes':p.stat().st_size} for p in inputs},
    'drafts':{n:sha(D/n) for n in ['README.md','formalization.yaml','ARCHIVE-AND-INSTALL-PLAN.json']},
    'exact_advertised_exports':names,'permitted_axioms':axioms,'definition_exceptions':[],
    'intended_project_markdown_links':links,
    'external_validator_overlay':{str(p.relative_to(D)):sha(p) for p in sorted(V.iterdir()) if p.is_file()},
    'proof_Lean_builds_run':False,'local_Lake_or_dependency_work':False,
    'live_changes_commits_pushes_status_changes':False,'Linux_Comparator_controls':'pending',
    'coordinator_acceptance':entry(acceptance)
}
(D/'DRAFT-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'draft_readme_sha256':sha(D/'README.md'),'draft_metadata_sha256':sha(D/'formalization.yaml'),
                  'archive_plan_sha256':sha(D/'ARCHIVE-AND-INSTALL-PLAN.json'),
                  'checks_sha256':sha(D/'DRAFT-CHECKS.json'),'exports':len(names)},indent=2))
