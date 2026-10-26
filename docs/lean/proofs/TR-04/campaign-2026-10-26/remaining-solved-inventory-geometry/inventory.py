#!/usr/bin/env python3
"""Read-only registry/live-source triage; writes only this report directory."""
from pathlib import Path
import collections,datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[5]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
registry=REPO/'problem_ids.json';reg=json.loads(registry.read_text())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
prior_path=REPO/'docs/lean/campaign-2026-10-17/inventory/inventory.json';prior=json.loads(prior_path.read_text())['published']
counts=collections.Counter();entries=[];status_by_id={}
notes={
 'IE-21':'Only zero-vector/empty-row-energy legacy lemmas; concrete OriginalLimitTarget and QuantitativeAnswerTarget are both still unproved.',
 'IV-02':'Only rotation/layer-count support. Solved means NP-hard/Target iff P=NP classification; affirmative Target alone is not a proved resolution.',
 'IV-04':'Only 2x2 inverse-corner support. Solved means Target iff P=NP; old HullCase incorrectly required interval-shaped projection rather than its hull.',
 'MD-06':'Only projection from assumed abstract stable event. Original Target tends to1 but credited resolution tends to0; NegativeResolution/QuantitativeResolution must be proved separately.',
 'SP-14':'90 shared support modules and conditional gap/base-symbol results; final perturbed infinite symbol, two-sided nonextension and unconditional counterexample are missing.',
 'TR-04':'Full immutable concrete Target proof and canonical package fresh kernel evidence exist; draftPR370/actualCI acceptance pending per parent. Root-owned, exclude new work.',
 'RE-06':'Parent explicitly identifies another chat as owner; absence of live proof sources here is not absence of active work. Exclude reassignment.',
 'RE-05':'Root is developing isolated independence-free actual attained-optimum gate; no full probability/query proof yet. Coordinate, do not duplicate implementation.'}
for ident,rel in reg.items():
 p=REPO/rel;s=p.read_text();status=re.search(r'^\*\*Status:\*\* (.+)$',s,re.M).group(1).strip();counts[status]+=1;status_by_id[ident]=status
 if status!='Solved':continue
 key=ident.replace('-','');proofdir=REPO/'lean-statements/NLA/Proofs'/key;proofs=sorted(proofdir.glob('*.lean'))
 stmt=REPO/'lean-statements/NLA/Statements'/f'{key}.lean';reviewed=REPO/'lean-statements/Reviewed'/f'{key}.lean'
 canonical=[]
 for name in ['Solution.lean','FullSolution.lean']:
  q=p.parent/'lean'/name
  if q.exists():canonical.append(dict(path=str(q.relative_to(REPO)),sha256=h(q),explicit_theorems=re.findall(r'^\s*theorem\s+([\w.]+)',q.read_text(),re.M)))
 if ident=='TR-04':kind='root_full_proof_acceptance_pending'
 elif ident=='RE-06':kind='external_owner_excluded'
 elif ident=='RE-05':kind='root_active_isolated_gate_not_full_proof'
 elif ident in ['IE-21','IV-02','IV-04','MD-06','SP-14']:kind='support_only_not_full_proof'
 else:kind='statement_only_no_live_proof_found'
 entries.append(dict(id=ident,canonical_readme=rel,title=s.splitlines()[0].removeprefix('# '),readme_sha256=h(p),statement=dict(path=str(stmt.relative_to(REPO)),sha256=h(stmt)),reviewed_statement=dict(path=str(reviewed.relative_to(REPO)),sha256=h(reviewed))if reviewed.exists()else None,canonical_solution_files=canonical,shared_proof_source_count=len(proofs),shared_full_target_candidate=(proofdir/'Final.lean').exists()or(proofdir/'MachineTTFull.lean').exists(),assessment=kind,notes=notes.get(ident,'The concrete reviewed Target is present; no canonical Solution or shared proof source found in this clone. This is source-presence triage, not a proof of nonexistence elsewhere.')))
assert len(entries)==32 and counts['Lean verified']==86
assert len(reg)==217
review_checks=[]
for name in ['lean-boundary-inventory.json','lean-boundary-statement_design.json']:
 p=REPO/'docs/lean/statements/IE-21/reviews'/name;d=json.loads(p.read_text());mismatch=[]
 for rel,sha in d['input_sha256'].items():
  if h(REPO/rel)!=sha:mismatch.append(rel)
 assert not mismatch
 review_checks.append(dict(path=str(p.relative_to(REPO)),sha256=h(p),verdict=d['verdict'],all_bound_live_inputs_exact=True))
evidence_paths=['docs/lean/campaign-2026-10-17/inventory/README.md','docs/lean/campaign-2026-10-17/inventory/inventory.json','docs/lean/proofs/TR-04/campaign-2026-10-23/NEXT_TARGET_INVENTORY.json','docs/lean/proofs/FR-05/INDEPENDENT_REVIEW.md','docs/lean/proofs/FR-05/LINUX_CI_RECEIPT.md','linear-systems-and-elimination/IE-21/lean/Solution.lean','linear-systems-and-elimination/IE-21/lean/Definitions.lean','docs/lean/statements/IE-21/NUMERICAL_TARGETS.md','docs/lean/statements/IE-21/ORIGINAL.md','lean-statements/NLA/Statements/IE21.lean','lean-statements/Reviewed/IE21.lean','lean-statements/NLA/Statements/RowDeletion.lean','references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex','references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md','lean-statements/NLA/Proofs/IE22/Final.lean','lean-statements/NLA/Proofs/IE22/TrimmingDual.lean','lean-statements/NLA/Proofs/IE22/GaussianTrimming.lean','lean-statements/NLA/Proofs/IE22/EnergyBounds.lean','lean-statements/NLA/Proofs/IE22/NormalizedGaussianRows.lean','lean-statements/NLA/Proofs/IE22/NormalizedGaussianApprox.lean','docs/lean/statements/IV-02/NUMERICAL_TARGETS.md','docs/lean/statements/IV-04/NUMERICAL_TARGETS.md','lean-statements/NLA/Statements/IV02.lean','lean-statements/NLA/Statements/IV04.lean','lean-statements/NLA/Statements/MD06.lean','lean-statements/NLA/Statements/RE05.lean','lean-statements/NLA/Computation/LinearFamilyQuery.lean','lean-statements/NLA/Computation/NonadaptiveMatrixQuery.lean','lean-statements/NLA/Proofs/TR04/Optimum.lean','lean-statements/NLA/Proofs/TR04/SVDTotal.lean','lean-statements/NLA/Proofs/SP14/SubsequenceGap.lean']
evidence=[dict(path=rel,sha256=h(REPO/rel))for rel in evidence_paths]
result=dict(reviewer='/root/recover_geometry',observed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),observed_head=head,scope='Read-only current registry/live-source fidelity triage in this clone; no proof/CI/Comparator/status approval, external browsing or original/package edits. Other-chat ownership only as explicitly supplied by parent.',registry=dict(path='problem_ids.json',sha256=h(registry),registered_ids=len(reg)),status_counts=dict(counts),remaining_solved=len(entries),excluded_new_assignment=['TR-04','RE-06'],root_active_gate='RE-05 actual attained Frobenius optimum; mutable development, not full Target',next_unowned_full_problem='IE-21',next_coordinated_small_gate='RE-05 attained optimum (root already owns)',prior_published_solved=len(prior['solved_ids']),since_prior_published_now_Lean_verified=[i for i in prior['solved_ids']if status_by_id[i]=='Lean verified'],FR05=dict(status=status_by_id['FR-05'],disposition='Already full proved with isolated Linux Comparator/LeanCert receipt; do not re-prove.'),IE21=dict(literal_target='NLA.Statements.IE21.Target = OriginalLimitTarget ∧ QuantitativeAnswerTarget',renewed_boundary_hash_checks=review_checks,canonical_original_byte_identity=(REPO/'linear-systems-and-elimination/IE-21/README.md').read_bytes()==(REPO/'docs/lean/statements/IE-21/ORIGINAL.md').read_bytes(),workload=['Actual UniformSphere probability and polar Gaussian/radius law; exact sqrt(2/n) coupling, not the weaker existing IE22 bound.','Pointwise bounded trimming/Hoeffding and covariance concentration with exact 2*9^n*exp(-m*t^2/512),5*exp(-2*m*eta^2); full direction nets and simultaneous bad event.','Deterministic variational/floor/ratio assembly and varying-dimension limit using only n→∞ and m/n→∞; keep OriginalLimitTarget separately exported.'],reuse_limits='IE22 provides deterministic energy/trimming, Gaussian quantile identities and actual normalized Gaussian row definitions; its finite-sample existence and weaker expectation error do not imply the literal quantitative spherical probability theorem.'),IV_classification_fidelity=dict(IV02='Preserve original affirmative algorithm-existence Target; credited theorem is Target ↔ PEqualsNP, not Target. Old arbitrary Prop complexity contract is vacuous.',IV04='Preserve original affirmative algorithm-existence Target; credited theorem is Target ↔ PEqualsNP, not Target. Old HullCase projection interval shape is false on disconnected projections. Correct concrete Target includes empty/unbounded exact hulls.'),RE05_reuse=dict(no_existing_equivalent_proof_found_before_root_gate=True,root_mutable_gate_path='lean-statements/NLA/Proofs/RE05/Attained.lean',literal_component='NLA.Statements.RE05.AttainedOptimum',stronger_valid_route='No independence assumption is needed for minimization over the finite-dimensional range of represent P.',pinned_Mathlib_API='Submodule.exists_norm_eq_iInf_of_complete_subspace in Analysis/InnerProductSpace/Projection/Minimal.lean:231',sInf_transport='Use exact Euclidean flatten/Frobenius identity and range-submodule minimizer, then IsLeast.csInf_eq for actual LinearFamilyQuery.optimum; TR04.Optimum is a proof-pattern reuse, not a drop-in theorem.',remaining_full_target='SVDTotal and the complete Gaussian success/query-count OriginalClaim and SourceCompanion remain required; attained optimum alone is not Target.'),entries=entries,evidence=evidence)
(HERE/'inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(head=head,counts=dict(counts),remaining=len(entries),assessment_counts=dict(collections.Counter(e['assessment']for e in entries)),report_sha256=h(HERE/'inventory.json')),indent=2))
