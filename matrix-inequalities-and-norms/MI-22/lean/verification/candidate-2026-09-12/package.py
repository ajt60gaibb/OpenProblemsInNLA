from pathlib import Path
import hashlib, json, datetime, yaml
p=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
o=p/'verification/candidate-2026-09-12';o.mkdir()
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
f=json.loads((p/'verification/proof-freeze.json').read_text())
for rel,r in f['files'].items():assert sha(p/rel)==r['sha256'],rel
reports={'reviews/statement-referee-1.md':'13556154d85fefbf81b0171bf7ff9028478b2c15327c67c78f3dc7fd18a4129a','reviews/statement-referee-2.md':'abc0e176440936638ae20ce0b105bc823b125a3fb7eaeaf13f95ff3e14eda1f7','reviews/proof-referee-1.md':'250b98be84248ba8dcb1c9be0a1d60743b88d0aadf5919ac6baf601a6f9597c3','reviews/proof-referee-2.md':'b97c55e0d2667efa9b297039db26801f66af3a9cd80a8a2de39d45c1ce6a6e77'}
for rel,h in reports.items():assert sha(p/rel)==h,rel
(o/'inputs-before.json').write_text(json.dumps({'proof_freeze_sha256':sha(p/'verification/proof-freeze.json'),'files':f['files'],'reviews':reports},indent=2)+'\n')
(o/'README.statement.md').write_bytes((p/'README.md').read_bytes())
assert sha(o/'README.statement.md')==f['files']['README.md']['sha256']
(p/'README.md').write_text('''# MI-22 — complete Lean counterexample, Linux verification pending

**All eight target exports are proved and have two independent statement approvals and two independent final proof approvals.** Local checks passed using only the standard three axioms. The actual Linux sandboxed Comparator/default-kernel run and its independent operational audit are still pending. The canonical problem remains **Solved**.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. AI-assisted implementation by agent `/root/leancert_examples`; that implementer is not counted as an independent referee. Matthew J. Colbrook retains attribution for the original negative resolution and mathematical method.

## Full original scope and adapted witness

The [canonical target](../README.md) quantifies every positive dimension, every complex positive-definite pair A,B and every real t in [0,1]. The actual weighted product is `A^t (A #_t B) B^(1-t)`. Its claimed singular-value log-majorization includes every proper prefix inequality **and equality of the full products**. The final export negates that entire original statement.

The formalization preserves the source's diagonal A, but uses the disclosed exact rational adaptation **B=D T⁸ D**, not Colbrook's printed integer B. The exact T, its source provenance and every required certificate are fixed in [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) and [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md). Their statement-stage descriptions are historical records preserved byte for byte. This project does not advertise a verification of the original printed B, its residual-to-root lemma or the source's 10900/10200 thresholds.

All powers are genuine Mathlib CFC powers, and all singular values are the actual descending Euclidean-map singular values, retaining multiplicities. The generic exported theorems prove their spectral semantics and the genuine operator/Frobenius/action bounds. Exact LDL and matrix algebra prove positivity and all numerical certificates as conclusions. For the actual root Y=B^(1/8), the proof establishes Y⁸=B and the noncommuting identity L Y=N. The positive trace bound gives ‖Y‖₂<4; an exact unit-vector coordinate exceeds 44000, forcing ‖L‖₂>11000. The exact Frobenius estimate gives ‖AB‖₂<10500. Thus the actual first singular values reverse the required k=1 inequality at n=3,t=1/8, refuting the full universal statement.

## Files and exported results

- [Definitions](NLA/MI22/Definitions.lean) and the independently approved [Challenge](Challenge.lean) state the unchanged mathematical boundary.
- [FunctionalCalculus](NLA/MI22/FunctionalCalculus.lean), [Norms](NLA/MI22/Norms.lean) and [SingularValues](NLA/MI22/SingularValues.lean) establish genuine generic semantics.
- [Witness](NLA/MI22/Witness.lean), [ExactData](NLA/MI22/ExactData.lean) and [Proof](NLA/MI22/Proof.lean) prove every finite certificate, true root identity and contradiction.
- [Solution](Solution.lean) exports `singular_values_semantics`, `spectral_power_semantics`, `euclidean_norm_bounds`, `witness_rational_data`, `witness_principal_powers`, `witness_operator_gap`, `counterexample` and `not_weightedLogMajorizationConjecture`, all in namespace `NLA.MI22`.
- [formalization.yaml](formalization.yaml) follows the actual pinned v0.4 metadata schema. [comparator.json](comparator.json) selects exactly those eight exports, allows only the standard three axioms and has no definition exceptions.

## Reproduction and precise trust scope

From this project directory, build the **complete proof** explicitly:

```
lake build Solution
```

The frozen default target remains Challenge, so plain `lake build` checks the statement target. The only authorized configuration change appended the Solution library; the [original lakefile](verification/lakefile.statement.toml) and [exact authorization/diff](verification/build-registration.json) remain intact.

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` are pinned. The complete solution closure has zero admissions and exactly `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Challenge's eight intentional placeholders are isolated and never imported by Solution.

LeanCert proves the retained scalar comparison **10500<11000** in explicit kernel mode, on the singleton [0,0]. Its exact Boolean certificate is kernel-proved and consumed in the strict singular-value reversal and full negation. It certifies only this scalar separation. Matrix tables, positivity, CFC roots and norm bridges are proved with exact Lean mathematics. Three squarings and one tested row avoid matrix-root approximation, interval subdivisions and numerical singular-value computation.

The [author's completion record](reviews/proof-completion.md) and [proof freeze](verification/proof-freeze.json) bind 104 original project inputs and eight original source files. Both final referees freshly rebuilt actual proof modules in separate prefixes excluding prior project objects; they reused clean pinned dependency caches and did not claim full dependency-source rebuilds. They inspected actual declaration dependencies, all 17 internal/public standard-three reports and the retained LeanCert certificate.

## Independent reviews and remaining checks

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Final proof referee 1: [report](reviews/proof-referee-1.md), [independent raw evidence](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json).
- Final proof referee 2: [report](reviews/proof-referee-2.md), [independent raw evidence](reviews/proof-referee-2-root-evidence/manifest.json).

These are independent AI-agent reviews applying the [NLA adaptation of Tau Ceti standards](../../../docs/lean/REVIEW.md), not human peer review or source-author endorsement. Local macOS checks and exact signature comparison do not replace the [required Linux verification pipeline](../../../docs/lean/README.md). No Linux result or immutable submitted proof revision is claimed yet.

The [archived statement-stage README](verification/candidate-2026-09-12/README.statement.md) preserves the original frozen bytes. Candidate packaging changes only this current README among the 104 proof-freeze inputs; all mathematical source, Challenge, numerical targets, source mapping, configuration, pins and review evidence remain unchanged. The candidate integrity record and handoff are retained in [verification/candidate-2026-09-12](verification/candidate-2026-09-12/).
''')
# The correct repository-root relation is three parents above this project's directory.
base='https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc/'
exports=json.loads((p/'comparator.json').read_text())['theorem_names']
ax=['propext','Classical.choice','Quot.sound']
scopes=[
'Generic nonnegativity, descending order, zero extension, full adjoint-composition eigenvalue square-root semantics and first-value/operator-norm identity for actual Mathlib singular values.',
'Principal spectral meaning of genuine CFC powers for every complex positive-definite matrix and every real exponent.',
'Actual Euclidean operator-norm squared Frobenius upper bound and action-coordinate bound for every complex matrix and every Euclidean vector.',
'All exact LDL, diagonal, positivity, unit-vector, trace, tested coordinate and full squared Frobenius certificates for the disclosed rational adaptation, as conclusions.',
'Every genuine principal-power identity, positivity of the actual root, the original-order noncommuting product reduction L Y=N and the actual root-norm bound.',
'Strict actual operator-norm bounds below 10500 for AB and above 11000 for the canonical left product.',
'Full original admissibility at n=3,t=1/8, strict first-singular-value reversal and failure of full singular-value log-majorization.',
'Unconditional negation of the full original universal complex positive-definite/all-dimensions/all-parameters conjecture, with every prefix and full-product equality retained.'
]
m={
'version':'v0.4',
'project':{'name':'MI-22: Lemos–Soares singular-value log-majorization counterexample','description':'Complete negative resolution of the canonical complex positive-definite weighted singular-value log-majorization statement, using an exact rational adaptation and proved genuine CFC, singular-value and Euclidean-norm semantics.','authors':['George Stepaniants'],'affiliations':{'George Stepaniants':'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'},'responsible_maintainers':['George Stepaniants'],'license':'Apache-2.0'},
'repository':{'role':'substantive-development'},
'sources':[{'title':'MI-22 — Lemos–Soares singular-value log-majorization','id':base+'matrix-inequalities-and-norms/MI-22/README.md','type':'web-post','location':'Complete original canonical problem statement','relationship':'formalizes','author_endorsement':'not-contacted','note':'All positive dimensions, all complex positive-definite A,B and every t in [0,1], including every proper singular-value prefix inequality and equality at the full dimension.'},{'title':'MI-22: a certified operator-norm counterexample to the weighted log-majorization','authors':['Matthew J. Colbrook'],'id':base+'references/colbrook-matrix-2026-09-11/original-proofs/MI-22.tex','type':'manuscript','location':'Complete theorem and counterexample method; see SOURCE_CORRESPONDENCE.md for the disclosed changed witness','relationship':'adapts','author_endorsement':'not-contacted','note':'The original negative resolution and mathematical method remain Colbrook’s. This formalization preserves his diagonal A but defines a different rational B=D T^8 D using an exact dyadic adaptation of his root approximation R. It does not claim to formalize the printed integer B, source root-error theorem, residual bounds or original 10900/10200 thresholds.'}],
'related_formalizations':[{'id':'https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof','relationship':'other','note':'Campaign workflow example for statement-first structure, kernel-only LeanCert and the shared Comparator pipeline; no Forsythe mathematical theorem is assumed.'},{'id':'https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1','relationship':'other','note':'Campaign reference for separating actual targets and mathematical definitions from proof implementation; no Schiffer theorem is imported.'}],
'automation':{'methods':[{'method':'agent','framework':'OpenAI Codex','tool_setup':'Multiple agents; two independent statement approvals before implementation, pinned Mathlib and LeanCert, then two independent final proof reviews with separate-prefix source elaboration and actual dependency/certificate inspection.','prompting_notes':'Keep the full complex positive-definite universal target, actual CFC powers, ordered singular values with multiplicities, true Euclidean norms and the complete log-majorization definition. Use the disclosed exact rational B=D T^8 D, exact LDL and three squarings; leave the other root as the actual CFC root and prove L Y=N in the original factor order. Prove every positivity and numerical certificate as a conclusion. Retain the explicit kernel LeanCert point inequality 10500<11000 in the final strict reversal.'}],'notes':'AI-assisted formalization requested by George Stepaniants. Implementation agent /root/leancert_examples is not an independent referee. No human review, source-author endorsement, historical priority, unrecorded model identity or measured cost is claimed.'},
'status':{'scope':'Complete local proof of the full canonical negative resolution, with all eight exports approved by two independent statement referees and two independent final proof referees. Local separate-prefix builds and transitive axiom checks passed. Actual Linux sandboxed Comparator/default-kernel execution, its controls, independent operational audit and publication review remain pending. Canonical status remains Solved.','sorry_count':0,'sorry_in_definitions':0,'axioms':ax,'main_results':[{'declaration':e,'file':'Solution.lean','sorry_count':0,'axioms':ax,'comparator_config':'comparator.json','literature_dependencies':[]} for e in exports]},
'fidelity':{'divergences':'No narrowing of the original target. The witness B differs from Colbrook’s printed integer B and is explicitly defined by an exact eighth-power congruence; source thresholds change to 10500 and 11000. All principal-power, positivity, actual norm and ordered singular-value bridges are proved rather than assumed. Every original complex input quantifier, all real t in [0,1], every proper prefix and full-product equality remain in the conjecture. A first-prefix violation at n=3,t=1/8 refutes the entire conjunction. The original printed witness and root-error lemma are not advertised as formalized.'},
'review':{'status':'agent-reviewed; actual Linux Comparator/default-kernel verification pending','reviewers':['OpenAI Codex agent /root/solved_statement_inventory: independent statement referee 1 and final proof referee 1','OpenAI Codex agent /root: independent statement referee 2 and final proof referee 2'],'notes':'Both statement reports precede implementation; all mathematical statements, targets, source correspondence and pins remain unchanged. Both final referees checked the complete actual proof and fresh compiled dependencies, with 17 internal/public standard-three reports and 195 project declarations inspected. Referee 1 independently parsed and reconstructed 48 actual Lean rational-table entries and printed the auxiliary kernel Boolean checker proof. The retained LeanCert task is only 10500<11000 on [0,0], explicitly kernel checked and consumed in the full negation; other matrix and analytic obligations use exact Lean proofs. The only authorized build change appended the Solution lean_lib, with the exact original lakefile archived and defaultTargets Challenge retained; complete proof command is lake build Solution. The eight Challenge placeholders remain isolated from Solution. Candidate packaging archives the original frozen README and updates only the current README among the 104 proof-freeze inputs; all other 103 and eight original sources remain unchanged. Historical statement-stage language in the frozen numerical/source-mapping documents is preserved and labeled historical. Local macOS checks reused ten clean pinned dependency caches; they are not Linux Comparator runs or complete dependency-source rebuilds. Relevant Tau Ceti standards are adapted to NLA; no official endorsement is claimed.','statement_reports':[{'file':rel,'sha256':h} for rel,h in reports.items() if '/statement-' in rel],'proof_reports':[{'file':rel,'sha256':h} for rel,h in reports.items() if '/proof-' in rel],'proof_freeze':{'file':'verification/proof-freeze.json','sha256':sha(p/'verification/proof-freeze.json')},'linux_verification':{'status':'pending','note':'No MI-22 Linux run, successful Comparator result, default-kernel replay, controls or operational audit is claimed yet. Shared infrastructure success does not verify this problem.'}},
'alignment':[{'declaration':e,'scope':s} for e,s in zip(exports,scopes)],
'acknowledgements':'Matthew J. Colbrook for the original negative resolution and mathematical strategy; Mathlib and LeanCert contributors for genuine CFC, singular-value, matrix positivity, norm and certificate APIs. The code credits its campaign MI-23/MI-29 organization and re-proves every helper on this project’s definitions; no neighboring theorem is imported as an unproved premise. The shared Comparator and sandbox harness retain their licenses and attribution.'}
(p/'formalization.yaml').write_text('# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json\n'+yaml.safe_dump(m,allow_unicode=True,sort_keys=False,width=100))
(o/'package.py').write_bytes(Path(__file__).read_bytes())
print('Wrote current README, actual v0.4 metadata and byte-identical statement README archive.')
