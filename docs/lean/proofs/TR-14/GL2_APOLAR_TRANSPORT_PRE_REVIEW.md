# TR-14 chart apolar transport: exact pre-implementation contract

**Author:** /root/tr14_frob_review (AI agent), 10 October 2026. **Status:** mathematical and proposed Lean contract, frozen for independent review **before** implementation. This is the next stage after the audited homogeneous substitution module. It does not assert rank preservation, a normalized minimal polynomial, or the frozen all-width Target.

## Exact coefficient and moment objects

Let `V_d = BinaryForm d` be the genuine homogeneous binary-form submodule in the audited `GL2Homogeneous.lean`. Its zero-based monomials are `B_{d,i}=X^(d−i)Y^i`, `0≤i≤d`. For every `d≥0`, construct and prove an actual complex-linear equivalence

\[
  \operatorname{form}_d:\mathbb C^{d+1}\simeq_{\mathbb C}V_d,
  \qquad \operatorname{form}_d(g)=\sum_{i=0}^{d}g_i B_{d,i}.
\]

The inverse `coeff_d` must recover **every** `g_i`, including `i=0,d`, and `form_d(coeff_d P)=P` for every homogeneous `P`, including zero. This requires proving that a two-variable homogeneous polynomial has no monomials outside total degree `d` and that each such monomial has the unique exponent pair `(d−i,i)`. Merely defining a coordinate map without these inverse identities is insufficient. At `d=0`, the single basis element is `1`; no implicit positive-degree assumption is allowed. The map is linear over ℂ, with no conjugation or binomial scaling.

For every `D≥0` and frozen moment vector `h:Fin(D+1)→ℂ`, define a specific homogeneous dual functional

\[
  L_h(P)=\sum_{j=0}^{D} h_j\,\operatorname{coeff}_D(P)_j.
\]

Prove `L_h(B_{D,j})=h_j` for **every** `j:Fin(D+1)`, and prove `momentCoordinates L_h=h`. Conversely, for every complex-linear `L:V_D→ℂ`, prove `L_(momentCoordinates L)=L`. Thus moment vectors and homogeneous duals are inverse linear coordinate descriptions; `h=0 ↔ L_h=0`. This functional is *not* the polynomial `F(x,y)=Σ_j binom(D,j)h_jx^(D−j)y^j` in the canonical solution: the binomial coefficients belong to that associated binary form, not to the dual evaluation on the monomial basis. The audited `momentCoordinates` fixes the unweighted convention.

## Exact apolar pairing in every permitted degree

Fix `0≤d≤D` and set `e=D−d`. For `g:Fin(d+1)→ℂ` and `q:Fin(e+1)→ℂ`, put `G=form_d(g)` and `Q=form_e(q)`. Multiplication in the audited `binaryMul` has degree `d+e=D`, and its monomial products obey

\[
  B_{d,i}B_{e,j}=B_{D,i+j}
  \quad(0≤i≤d,\;0≤j≤e),
\]

with exact bounded index `i+j≤D`. Therefore

\[
  L_h(GQ)=\sum_{j=0}^{e}\sum_{i=0}^{d}q_jg_i h_{i+j}.
\]

The frozen audited `IsApolar h d hd g` is *exactly* `Σ_{i=0}^d g_i h_{i+j}=0` for every `j:Fin(D−d+1)`. Prove the two directions without dropping any equation:

\[
  \operatorname{IsApolar}(h,d,g)
  \iff
  \forall Q\in V_{D-d},\ L_h(GQ)=0.
\]

The forward direction expands an arbitrary homogeneous `Q` in its complete coefficient basis; the reverse direction tests each `Q=B_{D−d,j}`. The statement must also hold at `d=0` (one `g` coefficient, all `D+1` shifts), `d=D` (one shift, all `D+1` `g` coefficients), `D=0` (one scalar equation), `D=1`, and at balanced degrees. There is no monicity, nonzero-moment, least-degree, or genericity premise here.

## Inverse-dual chart transport in all degrees

For every `z:ℂ`, use the already audited `chartPhiEquiv z d`, whose forward substitution is `(X,Y)↦(Y,X+zY)` and inverse substitution is `(X,Y)↦(Y−zX,X)`. Define the transformed moments by the **inverse-dual** action

\[
  h^z=\operatorname{momentCoordinates}
     (\operatorname{chartMoment}(z,L_h)),
  \qquad L_{h^z}=L_h\circ(\operatorname{chartPhiEquiv}(z,D))^{-1}.
\]

The second equality must be proved from the complete moment-coordinate equivalence, not assumed. For **every** `d≤D` and every `g:Fin(d+1)→ℂ`, define its transported vector by

\[
  g^z=\operatorname{coeff}_d
        (\operatorname{chartPhiEquiv}(z,d)(\operatorname{form}_d(g))).
\]

Then prove the exact all-degree equivalence

\[
  \operatorname{IsApolar}(h,d,g)
  \iff
  \operatorname{IsApolar}(h^z,d,g^z).
\]

For the forward direction, every transformed test form `Q'∈V_{D−d}` must be obtained as `chartPhiEquiv z (D−d) Q`; this uses surjectivity of that equivalence. Apply the previously audited `chartMoment_mul_pairing` and the pairing characterization above. Reverse by the inverse equivalence. The same argument works at `d=0,D`, because `chartPhiEquiv` exists in degree zero. Prove also `g^z=0 ↔ g=0`, `h^z=0 ↔ h=0`, and that the transported degree-`d` apolar kernel is precisely the image of the original kernel. These are algebraic consequences of the coordinate and substitution equivalences, not extra assumptions. In particular the set of degrees `d≤D` admitting a nonzero apolar vector is identical before and after this chart change; the positive least degree supplied by the audited `minimal_apolar_exists` is preserved whenever `D≥1` and `h≠0`. Do not promote that corollary to a chart normalization theorem: choosing `z` and scaling a particular form are later work.

## Proposed Lean boundaries

The following are signature sketches. `hd:d≤D` supplies exact index bounds, and all displayed equations are intended as actual kernel-checked theorems, not `sorry` or custom axioms.

```lean
formEquiv (d : ℕ) : (Fin (d+1) → ℂ) ≃ₗ[ℂ] BinaryForm d
formEquiv_apply_monomial (d) (i : Fin (d+1)) :
  formEquiv d (Pi.single i 1) = binaryMonomial d i
homogeneousMoment {D} (h : Fin (D+1) → ℂ) : BinaryMoment D
momentCoordinates_homogeneousMoment (h) :
  momentCoordinates (homogeneousMoment h) = h
homogeneousMoment_momentCoordinates (L : BinaryMoment D) :
  homogeneousMoment (momentCoordinates L) = L
apolar_iff_product_annihilation (hd : d ≤ D) (g) :
  IsApolar h d hd g ↔
    ∀ Q : BinaryForm (D-d),
      homogeneousMoment h (binaryMul (formEquiv d g) Q) = 0
transformedMoments (z : ℂ) (h) : Fin (D+1) → ℂ
transportedApolarVector (z : ℂ) (d : ℕ) (g) : Fin (d+1) → ℂ
transformedMoment_eq_chartMoment (z) (h) :
  homogeneousMoment (transformedMoments z h) =
    chartMoment z (homogeneousMoment h)
apolar_iff_chart_apolar (z) (hd : d ≤ D) (g) :
  IsApolar h d hd g ↔
    IsApolar (transformedMoments z h) d hd
      (transportedApolarVector z d g)
```

The implementation may split coefficient equivalence, pairing, and apolar transport into separately audited modules. No original-coordinate catalecticant rank theorem, mode tensor action, ordinary/symmetric width transport, monic chart choice, or full `NLA.Statements.TR14.Target` follows from this stage alone. The chart map here is the explicit invertible one already proved; an arbitrary-`GL₂` API is not required to prove these formulas.

## Source locks and review gate

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` (§2) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Audited `lean-statements/NLA/Proofs/TR14/GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| Approved `GL2_CHART_TRANSPORT_PRE_REVIEW.md` | `5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322` |
| Approved `GL2_CHART_TRANSPORT_INDEPENDENT_PRE_REVIEW.md` | `0b225faaed0d307e582bc75946b540e872d1fdad927495e27d18f847d0b0ceb2` |
| Approved `GL2_HOMOGENEOUS_INDEPENDENT_FINAL_REVIEW.md` | `3f61314faeeafd5a24b050a4f83ecb6778ee78c43bb57813a6412a39255a5aa7` |

An independent mathematical review of this exact frozen document is required before Lean implementation. Changed contract bytes reopen that review. After implementation, exact source, proof escapes, imported LeanCert kernel, and transitive axioms require a separate final audit before aggregate import.
