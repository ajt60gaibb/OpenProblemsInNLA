# PR #169 — independent MI-26 fidelity review

**Verdict: PASS.** No original-target, function-class, order, or inspected proof-source blocker was found. The formal result is a complete negative answer to the canonical MI-26 assertion. Status promotion additionally requires the authenticated CI/Comparator/kernel gate assessed separately by the integration owner.

Reviewer: OpenAI Codex AI agent `/root/audit_functions_randomized`, independent of this PR's formalization implementation. Phase: final English-to-Lean and proof-source review. Date: 2026-09-12. Exact reviewed head: `38122892d2d6e6e0093a381dbfe2fbae026ac15b`, read in `/private/tmp/nla-lean-audit-169`. No repository edit, Git mutation, contributor-code execution or workflow execution was performed.

Source locations below are relative to `matrix-inequalities-and-norms/MI-26/lean/` unless otherwise stated. I read the actual Definitions, Challenge, Solution and complete Proof, the canonical target, previous complete informal resolution, numerical targets, configuration, formalization metadata and applicable CONTRIBUTING/Lean review rubric. Submitted PASS labels did not supply the mathematical conclusions below.

## Original target and function class

The canonical problem asks about every positive dimension, arbitrary complex PSD A and B, and every real-valued concave function on [0,∞) with f(0) ≥ 0. The two unitaries may depend on A, B and f. The pre-formalization canonical statement at repository revision `5adea969c17391693978ada2674d25bb5c3daeb1` has exactly this target, and the current previous-resolution text preserves it.

The primary source supports the real-valued interpretation: [Audenaert–Kittaneh, §2, Problem 5 and equation (11)](https://arxiv.org/html/1201.5232) asks whether monotonicity can be removed while retaining concavity and f(0) ≥ 0. This is distinguished from that section's earlier globally nonnegative-valued norm inequalities. [Bourin–Lee, Theorem 3.1 and Remark 3.13](https://arxiv.org/html/1109.2384) likewise singles out removal of monotonicity. Consequently the witness f(t) = t−t² is admissible: f(0)=0, but f(2)=−2. Neither the original resolution nor this formalization refutes the narrower globally nonnegative-valued class. Adding that condition would change the target.

`Definitions.lean:26–27` uses precisely `ConcaveOn ℝ (Set.Ici 0) f ∧ 0 ≤ f 0`. The complete scalar equivalence at `Proof.lean:25–39` proves that this is exactly the canonical Jensen inequality for x,y ≥ 0 and 0 ≤ θ ≤ 1. The fixed domain's convexity is proved, not assumed as an additional property of f. There is no continuity, monotonicity, boundedness or global nonnegativity premise.

Representing f by a total function ℝ → ℝ does not narrow the half-line class. Any original function extends by evaluating it at max(t,0), and restriction returns the original function. Values at negative arguments are unrestricted. `Proof.lean:51–62` proves that two such extensions agreeing on [0,∞) yield identical functional calculus on every PSD matrix, using the actual nonnegative eigenvalues. Thus the extension does not alter any term of the conjecture, including A+B.

## Genuine functional calculus and matrix order

`Definitions.lean:32–34` uses actual real CFC in the complex matrix algebra; it does not define a special polynomial operator and call it the general matrix function. `Proof.lean:42–49` proves equality with the full finite spectral formula for every real-valued f and every Hermitian A, without a continuity premise. I read the exact pinned [Mathlib HermitianFunctionalCalculus source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean): `Matrix.IsHermitian.cfc_eq` accepts an arbitrary function because its restriction to the finite matrix spectrum is continuous. There is no hidden exclusion of concave functions discontinuous at the half-line endpoint.

`Definitions.lean:44–50` quantifies over every complex PSD pair and every admissible function, followed by existence of arbitrary complex unitary-group elements. `unitaryConjugate` at lines 37–40 is ordinary multiplication by U and its conjugate transpose. I checked the pinned [unitary-group source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/UnitaryGroup.lean): membership gives the usual UU*=U*U=I conditions, with no restriction to real matrices or an enumerated subset.

The `MatrixOrder` scope is explicitly selected. The pinned [matrix-order source, lines 48–60](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/Order.lean) defines A ≤ B as `(B−A).PosSemidef`. The final contradiction uses this genuine PSD order and its quadratic-form consequence, not entrywise order or merely a real-part comparison substituted for PSD.

## Independent witness reconstruction and proof path

The previous `../solution.tex`, Theorem 1.1, supplies the same projections P = diag(1,0), Q = vv* with v=(3/5,4/5), and w=(1,−2). I independently reconstructed the following with Python exact rational arithmetic, without executing contributor code:

\[
P^2=P,\quad Q^2=Q,\quad
P+Q=\frac1{25}\begin{pmatrix}34&12\\12&16\end{pmatrix},\quad
(P+Q)^2=\frac1{25}\begin{pmatrix}52&24\\24&16\end{pmatrix}.
\]

The Gram forms establish PSD over the complex field. The polynomial image is

\[
F=f(P+Q)=\frac1{25}\begin{pmatrix}-18&-12\\-12&0\end{pmatrix},\qquad
Fw=(6/25,-12/25)^T,\qquad w^*Fw=6/5>0.
\]

`Proof.lean:73–84` proves admissibility through the exact Jensen gap θ(1−θ)(x−y)². Lines 86–110 prove PSD and idempotence, without assuming either. The generic CFC-to-polynomial bridge at lines 64–70 establishes f(A)=A−A² for every Hermitian A. Lines 112–124 then derive the actual CFC values f(P)=f(Q)=0 and f(P+Q)=F. Lines 126–139 prove the nonzero vector, exact complex quadratic form and strictly positive scalar.

For every U,V, the right-hand side is zero. `Proof.lean:157–170` converts a supposed inequality F ≤ 0 to PSD of −F, extracts 0 ≤ w*(−F)w = −6/5, and obtains a contradiction using the explicit kernel scalar certificate. Lines 172–176 instantiate the full universal conjecture at n=2 and the proved admissible data. This proves its negation with no residual hypotheses. No normalization of w is required to test PSD; the unnormalized w is why the scalar is 6/5 rather than the positive eigenvalue 6/25.

The informal source's additional positive-definite perturbation is outside the seven exports and is explicitly excluded from the formal scope. The original problem allows PSD inputs, so this omission does not weaken the claimed full negative resolution.

## Trust and verification limits

The seven deliberate placeholders are confined to Challenge. Solution imports Proof, and Proof imports the independent Definitions, never Challenge. Inspection found no proof-side hole, custom axiom, native execution trust, unsafe implementation or command redefining the logical environment. The scalar certificate uses `interval_decide (trust := kernel)` and is consumed by the final contradiction. Comparator lists all seven exports, has no replaceable definition holes, and allows only `propext`, `Classical.choice` and `Quot.sound`.

An ordinary Git diff found the mathematical source and relevant build/comparator configuration unchanged from the README's immutable proof revision `81176af27e570b59ba1e1a0745e28944e7d57c03` to the reviewed head. Mathematical and formalization authorship, AI assistance and scope exclusions are accurately separated in the metadata. I did not run Lean locally or authenticate remote CI evidence; those mechanical/provenance checks belong to the integration owner's separate gate. This review supplies independent semantic and mathematical assessment, not a claim of external human peer review.
