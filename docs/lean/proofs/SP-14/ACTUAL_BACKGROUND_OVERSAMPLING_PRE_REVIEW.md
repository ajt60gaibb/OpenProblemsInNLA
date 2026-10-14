# SP-14: actual-background Sobolev oversampling gate

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical/numerical pre-implementation contract, awaiting independent review. The original negative `Target` is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. In particular this contract follows Proposition “The two-level isomorphism estimate” (lines 1316–1479), Corollary “Explicit parameters” (lines 1671–1776), Lemma “Oversampling from two Sobolev bounds” (lines 1780–1806), and Proposition “Two explicit analytic estimates would suffice locally” (lines 1809 onward). The abstract algebra is already frozen and audited in `SobolevOversampling.lean`, SHA-256 `fd9b5a433847dc8392070752a97244bebeedde08d4d7f7a198e24d64f6f27d77`. The literal weighted spaces and their sharp tail/lift estimates are frozen and independently audited in `WeightedSobolevPhysical.lean`, SHA-256 `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109`, and `WeightedSobolevOperators.lean`, SHA-256 `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1`.

## Actual background and operator; no hidden inverse premise

Let `g₀(s)=√(1+s⁻¹)` be the source's exterior branch, normalized to one at infinity. Let `P=P₋+P₊` be a **finite real Laurent polynomial** with strictly negative powers in `P₋`, strictly positive powers in `P₊`, and `P₋(-1)=P₊(-1)=0`. Put `g=g₀+P` and `h(s)=s g(s)²−1`. With `α=1/8` and `γ=2⁻¹⁰⁰⁰`, assume exactly the source's five strict bounds

\[
 \|h-s\|_{\mathcal W^{1+\alpha}}<\gamma,\quad
 \|P_-\|_{\mathcal W^0}<\gamma,\quad
 \|P_-/g_0\|_{\mathcal W^0}<\gamma,\quad
 \|g_0P_-\|_{\mathcal W^{1+\alpha}}<\gamma,\quad
 \|P_+\|_{\mathcal W^4}<\gamma.
\]

The Laurent/Wiener norms and the quotient `P₋/g₀` must be defined with the actual exterior branch and its removable contact value; these are not uninterpreted real-valued fields. The bounds imply the source's Jordan curve `Γ=h(𝕋)` and the normalized conformal map `f:𝔻→D`, `f(0)=0`, `f′(0)>0`, with real symmetry and `f(-1)=-1`. A formal intermediate may carry a proved `f` and these properties, but the **primary theorem** must derive them from the displayed background hypotheses and the source's conformal-coordinate lemmas, not assume an unrelated disk map.

For a polynomial `V(s)=∑_{d≥0}v_ds^d`, define the *actual* limiting Jacobian by the source's row functions, not by an arbitrary bounded map:

\[
 \mathcal J_gV(t)=-2\sum_{d\ge0}v_d[s^d]R_t(s)X_t(s).
\]

Equivalently it must match the exact boundary integral of Proposition “Exact limiting Jacobian as a boundary integral”, including `N_t(ζ)`, the denominator `(h(ζ)-t)²`, and the two Cauchy terms; equivalence between these definitions is an implementation obligation. On polynomial `x`, `(J⁰)⁻¹x` is the source's inverse triangular binomial transform, with coefficient `v_d=−(1/2)∑_{k≥d} binom(−1/2,k−d)x_k/(k+1)` (the sum is finite). Define

\[
 \mathcal A_g x = \bigl(\mathcal J_g((J^0)^{-1}x)\bigr)\circ f.
\]

This polynomial formula is the identity to extend. In particular, a Lean theorem with arbitrary `As,Ar` merely *named* `actualBackgroundOperator` would not meet the gate.

## Exact two-level conclusion and oversampling instantiation

Use the concrete weighted sequence spaces from the reviewed modules with `s=−1/4`, `τ=1/8`, `r=s+τ=−1/8`. Construct bounded complex-linear maps `A_s,B_s:H^s→H^s` and `A_r,B_r:H^r→H^r`. On every polynomial `x`, both `A_s x` and `A_r x` must have physical coefficients equal to the Taylor coefficients of the same `\mathcal A_gx` above. Prove both-sided inverse equations `A_sB_s=B_sA_s=I` and `A_rB_r=B_rA_r=I`, coefficient-preserving compatibility `ιA_r=A_sι` and `ιB_r=B_sι`, and all four bounds

\[
 \|A_s\|,\ \|B_s\|,\ \|A_r\|,\ \|B_r\|\le2^{100}.
\]

The source obtains compatibility first for the operators on the dense polynomial inputs, and for inverse maps by uniqueness on the weaker space; both steps require proof. The primary Lean theorem should conclude the existence of these **specific extensions and inverses** from the five background bounds, with exact polynomial agreement. It may be implemented through named intermediate theorems for endpoint extension, Cauchy projection, bare-operator factorization, conformal composition, and exterior-factor perturbation. It may not take the four norm bounds, invertibility, or compatibility as opaque hypotheses and then report them as established for `\mathcal A_g`.

Now take `θ=2⁻¹⁰⁰⁰⁰`, `σ=3/8`, and for every `m∈ℕ` set `h_m=⌊θm⌋`, `q_m=⌊σm⌋`. Prove `h_m≤q_m`; for `m>0`, `h_m/(q_m+1)<θ/σ<4θ`, while `m=0` has `h_m=q_m=0`. With `M_s=K_s=K_r=2¹⁰⁰`, the actual constants give

\[
 \varepsilon_m=2^{200}\left(\frac{h_m}{q_m+1}\right)^{1/8}
 <\tfrac12
 \quad(m\ge0).
\]

The source's loose comparison is `2²⁰⁰(4·2⁻¹⁰⁰⁰⁰)^{1/8}<1/2`. Applying the reviewed abstract theorem **to the actual four extensions** yields the displayed operator

\[
 E_m=P_{h_m}A_s(I-P_{q_m})B_sP_{h_m},\qquad
 R_m=P_{q_m}B_sP_{h_m}(I-E_m)^{-1},
\]

and all five conclusions: `‖E_m‖≤ε_m`, `IsUnit(I−E_m)`, `P_{q_m}R_m=R_m`, `P_{h_m}A_sP_{q_m}R_m=P_{h_m}`, and `‖R_m‖≤2¹⁰⁰/(1−ε_m)<2¹⁰¹`. These equations use the exact source cutoffs and include the empty `m=0` section. They are the intended public Lean signature after the actual-extension theorem is available.

## Exact rational numerical ledger

At `γ=2⁻¹⁰⁰⁰`, the source's bare-operator norm and inverse estimates are each below `2⁴⁰`, and the actual exterior-factor perturbation is below `2¹⁰⁰γ=2⁻⁹⁰⁰`. Its product with the bare inverse is below `2⁻⁸⁶⁰<1/2`; Neumann inversion then permits the deliberately loose `2¹⁰⁰` bounds at both `r=3/4` and `r=7/8`. The source separately records `‖B−I‖≤2²⁵γ=2⁻⁹⁷⁵<1/2` in the bare Cauchy factorization. These inequalities are exact powers of two, not floating-point checks.

For the oversampling comparison, set `u=2²⁰⁰(4·2⁻¹⁰⁰⁰⁰)^{1/8}≥0`. Then `u⁸=2¹⁶⁰⁰·4·2⁻¹⁰⁰⁰⁰=2⁻⁸³⁹⁸<2⁻⁸=(1/2)⁸`, so `u<1/2` exactly. For the first nonzero `h_m`, `m=2¹⁰⁰⁰⁰` gives `h_m=1`, `q_m=3·2⁹⁹⁹⁷`, and `h_m/(q_m+1)=1/(3·2⁹⁹⁹⁷+1)<(8/3)2⁻¹⁰⁰⁰⁰<4·2⁻¹⁰⁰⁰⁰`. This checks the floor orientation and the denominator `q_m+1` without rounding.

## Feasibility and remaining target gates

The final arithmetic instantiation is small once the actual extensions exist. The extension theorem is a **large analytic project**: the source's proof uses the endpoint extension and projection estimates, the range identification for `C_h`, fractional Sobolev composition by a boundary diffeomorphism, the negative-order Bergman multiplier bound, exact Cauchy/Jacobian identities, exterior-factor coefficient estimates, and the numeric constant ledger. These are genuine prerequisites, not interchangeable operator assumptions. No current SP-14 Lean module constructs this actual `\mathcal A_g` on the weighted sequence spaces or proves its compatible inverses. The forcing estimate, finite Jacobian replacement, nonlinear fixed point, packet norm budgets, both-sided nonextension, canonical gap, and original negative `Target` remain separate open obligations. Approval of this contract authorizes only incremental Lean source under separately audited mathematical interfaces; it is not approval to claim the full target.
