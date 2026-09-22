"""Create truthful pending-verification packaging only after the complete build."""
from pathlib import Path
import json, hashlib, re, datetime
import yaml

p=Path(__file__).resolve().parents[2]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipt=json.loads((p/'reviews/complete-author-evidence/receipt.json').read_text())
assert receipt['all_selected_targets_compiled'] and receipt['selected_target_count']==20
for f,h in receipt['source_hashes'].items():assert sha(p/f)==h,f
for f,h in receipt['mathematical_boundary_sha256'].items():assert sha(p/f)==h,f
names=json.loads((p/'comparator.json').read_text())['theorem_names']
solution='''/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.IE22.Final
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

'''
for name in names:solution+='#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
(p/'Solution.lean').write_text(solution)
lake=(p/'lakefile.toml').read_text().replace('defaultTargets = ["Challenge"]','defaultTargets = ["Solution"]')
assert 'name = "Solution"' not in lake
(p/'lakefile.toml').write_text(lake+'\n[[lean_lib]]\nname = "Solution"\n')
meta=yaml.safe_load((p.parents[1]/'IE-21/lean/formalization.yaml').read_text())
meta['project']['name']='IE-22: exact optimal uniform row-deletion singular-value constant'
meta['project']['description']='The literal supremum over every real unit-row matrix has sharp asymptotic constant sqrt(h_theta), with the exact finite projected-Gaussian certificate, an explicit uniform squared O_theta(n^(-1/6)) rate, matching deterministic spherical realizations, every high-aspect sequence limit, and failure of the original eventual-uniform property for every smaller constant.'
meta['sources'][0]['title']='IE-22 complete canonical problem and original solution'
meta['sources'][0]['id']=meta['sources'][0]['id'].replace('/IE-21/','/IE-22/')
meta['related_formalizations'].append({'id':'https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/1eb284b84ecc0d3c958d022b3e020be7fa111391/linear-systems-and-elimination/IE-21/lean','relationship':'builds-on','note':'All 31 mathematical sources vendored byte-identically with provenance in reviews/IE21-DEPENDENCY.json; rebuilt in this project. IE21 was independently reviewed and Linux kernel verified, then published in PR314 with full PR CI passing. No mutable local-path or compiled-artifact dependency.'})
meta['automation']['methods'][0]['tool_setup']='Pinned Lean 4.33.1, Mathlib and authentic LeanCert. Every project proof module, including the 31 vendored IE21 modules, rebuilt locally; all 20 exact frozen signatures and standard-three axiom closures passed. Authentic LeanCert assertions and full non-root Linux Comparator verification remain pending; cached local builds do not establish those gates.'
meta['automation']['methods'][0]['prompting_notes']='Preserve the complete original supremum, floor, unit-row, spectral, Gaussian, finite-bound, asymptotic and optimality statements. Independently review and freeze all exact definitions and numerical targets before implementation. Prove every analytic and spectral dependency without new axioms, assumed target conclusions, or dimension/aspect restrictions.'
meta['automation']['notes']='Substantial Codex assistance. ie21_final_fidelity authored the frozen IE22 boundary and TrimmingThreshold, GaussianMean, GaussianEnergy, ProjectionEvent and DeterministicBound. ie21_final_correctness authored VarianceTensorization and SpectralProjection. infrastructure_audit authored GaussianPoincare, GaussianPoincareHinge and GaussianVariance. Root authored SupremumSemantics, SphericalRealization, DeterministicSchedule, AsymptoticConclusion, Final and packaging. Root and infrastructure_audit independently approved the IE22 mathematical boundary before proof implementation; their prior IE21 authorship is disclosed. Incremental nonauthor module reviews explicitly disclose authorship elsewhere. A header-only correction to GaussianPoincare has additive evidence; historical hashes/reports are retained. Fresh final whole-source nonauthor reviews remain pending. No human peer review or official Tau Ceti endorsement is claimed.'
axioms=['propext','Classical.choice','Quot.sound']
main=[]
for name in names:
    short=name.rsplit('.',1)[1]
    files=[f for f in receipt['source_hashes'] if re.search(r'^theorem '+re.escape(short)+r'\b',(p/f).read_text(),re.M)]
    assert len(files)==1,(name,files)
    main.append({'declaration':name,'file':files[0],'sorry_count':0,'axioms':axioms,'comparator_config':'comparator.json','literature_dependencies':[]})
meta['status']={'scope':'All 20 required complete statements are proved locally, with exact frozen types and no additional final-target assumptions. Fresh final nonauthor whole-proof reviews and full authentic Linux/LeanCert/Comparator gates are pending. The canonical problem remains Solved; no status promotion follows from local compilation alone.','sorry_count':0,'sorry_in_definitions':0,'axioms':axioms,'challenge_placeholder_count':20,'completed_target_count':20,'local_development_build':'passed-all-proof-modules','comparator_result':'not-run','authoritative_linux_result':'not-run','main_results':main}
meta['fidelity']['divergences']='No weakening of the complete canonical target. M is the attained supremum of actual normalized floor-row singular values over every unit-row matrix. The finite projection and probability bounds, exact floor(n^(2/3)) and n^(-1/6) schedule, uniformity in all m, every high-aspect lower witness and limit, and no-smaller-constant quantifiers are proved. The source Hermite-series Poincare sketch is replaced by an exact elementary scalar crossing-kernel argument, actual nonsmooth hinge regularity and proved finite-product variance tensorization. This changes the proof route without assuming the desired variance estimate. The quantitative O_theta constant is explicitly 22+4L^2+8L, with L=2/(1-theta). Zero rows of projected matrices, rank deficiency and empty retained selections are included.'
meta['review']={'status':'preproof-boundary-approved-and-incremental-modules-reviewed; final-reviews-pending','notes':'Exact preproof and module-review hashes, independent roles and authorship limitations are retained. Final two fresh nonauthor whole-source reviews, authentic Linux evidence and independent operational completion reviews remain required before promotion or publication.'}
(p/'formalization.yaml').write_text(yaml.safe_dump(meta,sort_keys=False,allow_unicode=True,width=100))
(p/'README.md').write_text('''# IE-22: complete proof sources, final verification pending

This self-contained package proves all 20 independently reviewed statements for the complete original IE-22 target: the genuine supremum over every real unit-row matrix has the canonical sharp constant, with the exact finite bound, an explicit uniform squared error rate, deterministic near-extremizers along every high-aspect sequence, the supremum limit, and optimality of the original eventual-uniform property.

Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial AI-agent assistance and all proof/review roles are disclosed in formalization.yaml. No contact email is added.

All project proof sources, including the 31 byte-identical vendored IE-21 modules, were freshly compiled locally. The 20 exact frozen theorem types and transitive closures passed with only propext, Classical.choice and Quot.sound. Final nonauthor whole-source reviews and authentic Linux LeanCert/Comparator verification remain pending. The canonical problem remains Solved until all required gates pass.

Definitions, Challenge, NUMERICAL_TARGETS.md and comparator.json retain exactly the bytes approved before implementation; reviews/statement-freeze.json binds them. Historical unreviewed-draft wording in those immutable records describes that earlier stage. Their 20 deliberate Challenge placeholders establish no mathematics; no proof imports Challenge. Solution explicitly selects authentic LeanCert kernel trust and checks every selected theorem. The independent statement and solution environments are compared by the pinned real Comparator.

IE-21 is reused from its verified immutable source commit 1eb284b84ecc0d3c958d022b3e020be7fa111391, now published as reviewed PR314 with full PR CI passing. reviews/IE21-DEPENDENCY.json binds all 31 source files. This package rebuilds them and uses no mutable local-path dependency, dependency axiom or imported compiled artifact.

Reproduce on the documented non-root Linux environment using the unchanged shared repository infrastructure: `tools/lean/verify.sh linear-systems-and-elimination/IE-22/lean TOOLS_DIRECTORY`. Default `lake build` compiles Solution; the full verifier additionally runs actual isolation/rejection controls, separate Comparator exports, permitted-axiom checks and default-kernel replay. Local cached development receipts are explicitly distinct from those authoritative gates.

The proofs use exact algebra, real analysis, finite-dimensional spectral theory and probability. The sharp Gaussian variance constant is proved through a one-dimensional crossing-kernel identity, absolutely continuous hinge fibers and finite-product tensorization. No floating-point integration, arbitrary truncation or numerical eigenvalue search is used. The exact schedule yields C=22+4L^2+8L for L=2/(1-theta).
''')
timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
(p/'reviews/proof-source-freeze.json').write_text(json.dumps({'phase':'all 20 exact local proofs complete; final nonauthor and Linux gates pending','timestamp_utc':timestamp,'source_sha256':receipt['source_hashes'],'mathematical_boundary_sha256':receipt['mathematical_boundary_sha256'],'selected_target_count':20,'author_build_receipt_sha256':sha(p/'reviews/complete-author-evidence/receipt.json')},indent=2)+'\n')
core=list(receipt['source_hashes'])+['Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','Solution.lean','formalization.yaml','README.md','lean-toolchain','lakefile.toml','lake-manifest.json','LICENSE']
(p/'reviews/package-source-freeze.json').write_text(json.dumps({'phase':'complete source package ready for independent final review; authentic Linux gates pending','timestamp_utc':timestamp,'source_sha256':{f:sha(p/f) for f in sorted(core)},'selected_target_count':20,'mathematical_boundary_unchanged':True},indent=2)+'\n')
print('Prepared truthful pending-verification package and freeze:',len(core),'core files')
