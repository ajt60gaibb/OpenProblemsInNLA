# TR-14 finite chart and monic least-apolar form: exact pre-implementation contract

**Author:** /root/tr14_frob_review (AI agent), 10 October 2026. **Status:** frozen mathematical and proposed Lean contract for independent review **before** implementation. This stage starts from the audited all-degree apolar transport; it does not transport Hankel tensor widths or prove the frozen TR-14 Target.

## Exact finite chart and polynomial evaluation

For every natural degree `d`, use the audited coefficient equivalence `binaryFormEquiv d` and its zero-based basis `B_{d,i}=X^(d−i)Y^i`. For `g:Fin(d+1)→ℂ`, define the affine dehomogenization

\[
  p_g(t)=\sum_{i=0}^{d}g_i t^i=\operatorname{form}_d(g)(1,t).
\]

Prove `p_g.coeff i=g_i` for each `i:Fin(d+1)` and `p_g=0 ↔ g=0`. The proof must use the **complete** coefficient basis from `GL2CoefficientBasis.lean`, so a nonzero homogeneous form cannot disappear on the affine slice `X=1`. The statement includes `d=0` (a nonzero constant remains nonzero), and does not require `g_d≠0`; an initial root at infinity is allowed. Because ℂ is infinite, `g≠0` implies there exists `z:ℂ` with `p_g.eval z≠0`. This is a nonzero-polynomial existence argument, not numerical root finding or an unproved genericity choice.

The audited explicit chart is

\[
  T_z:(X,Y)\longmapsto(Y,X+zY),\qquad
  T_z^{-1}:(X,Y)\longmapsto(Y-zX,X),
\]

with determinant `−1`. For every `d` and every `z`, prove the **exact coefficient identity**

\[
  \bigl(\operatorname{transportedApolarVector}(z,d,g)\bigr)_d
  =\bigl(\operatorname{form}_d(g)\circ T_z\bigr)(0,1)
  =\operatorname{form}_d(g)(1,z)
  =p_g(z).
\]

Here evaluation at `(0,1)` selects the `Y^d` coefficient, with no binomial factor, conjugation, or index reversal. All four equalities should be proved for `d=0` too. Thus the selected `z` makes the transformed **last** coefficient nonzero, even if the original `g_d=0`. A proof only that some transformed coefficient is nonzero would not give the monic affine chart required downstream.

## Scaling and exact affine degree

Given such `z`, write `g^z=transportedApolarVector z d g`, `a=g^z_d≠0`, and `b_i=a⁻¹ g^z_i`. Then `b_d=1`, `b≠0`, and `b` is apolar for `h^z=transformedMoments z h` whenever `g` is apolar for `h`. Scaling must be proved using linearity of the **audited** `apolarMap`; it may not assume apolarity of `b`. Define

\[
  q(t)=p_b(t)=\sum_{i=0}^{d}b_i t^i.
\]

Prove `q.coeff i=b_i` for every `i≤d`, `q.Monic`, and `q.natDegree=d` **exactly**. In particular, no tacit cast from an upper degree bound to equality is allowed. This is the precise polynomial and coefficient vector required by the audited `NormalizedQuotient.lean` hypotheses. The monic condition is meaningful at the least apolar degree `d=r₀≥1`; the preliminary dehomogenization and evaluation identities still hold at `d=0`.

## Least-degree and nonzero-moment preservation

Fix `D≥1`, `h:Fin(D+1)→ℂ` with `h≠0`, and an **arbitrary** least-degree witness `1≤r₀≤D/2+1` as supplied by the audited `minimal_apolar_exists`: `r₀≤D`, a chosen `g:Fin(r₀+1)→ℂ` with `g≠0` and `IsApolar h r₀ hrD g`, and every smaller apolar kernel is zero. Do not assume the chosen `g` is unique, monic, squarefree, or has nonzero original last coefficient.

Choose `z` from the nonzero dehomogenization of **this** `g`. With `h^z=transformedMoments z h`, the audited `transformedMoments_eq_zero_iff` yields `h^z≠0`. The audited `apolar_iff_chart_apolar` transports the chosen apolar vector to `g^z`, and the scaling above gives an apolar monic `b`. For every `k<r₀` with `k≤D` and every `c:Fin(k+1)→ℂ`, prove

\[
  \operatorname{IsApolar}(h^z,k,c)\Longrightarrow c=0.
\]

This uses the audited exact kernel-image or `chart_nonzero_apolar_degree_iff` theorem in **every lower degree**, including `k=0`; checking only `k=r₀−1` is insufficient. The chosen `r₀` therefore remains the exact least nonzero apolar degree of `h^z`. The balanced endpoint `D=2r₀−2` may have a two-dimensional least kernel: normalize each **chosen** nonzero `g` without asserting uniqueness or choice independence. At `r₀=1` and `D=1`, the argument still works when the original form is a multiple of `X` (original final coefficient zero). The zero moment vector is a separate case in the frozen Target and is not assigned a positive least apolar degree.

## Proposed Lean boundaries

These are signature sketches; exact bounds and proof terms may be exposed explicitly. Every theorem must be kernel checked without `sorry`, custom axioms, or numerical sampling.

```lean
dehomogenize (d : ℕ) : (Fin (d+1) → ℂ) →ₗ[ℂ] Polynomial ℂ
dehomogenize_coeff (g) (i : Fin (d+1)) :
  (dehomogenize d g).coeff i.val = g i
dehomogenize_eq_zero_iff (g) : dehomogenize d g = 0 ↔ g = 0
chart_last_coefficient (z) (d) (g) :
  transportedApolarVector z d g ⟨d, by omega⟩ =
    (dehomogenize d g).eval z
exists_chart_last_nonzero (hg : g ≠ 0) :
  ∃ z : ℂ, transportedApolarVector z d g ⟨d, by omega⟩ ≠ 0

normalize_chosen_minimal_apolar
    (hD : 1 ≤ D) (hh : h ≠ 0) (hrD : r₀ ≤ D)
    (hrLo : 1 ≤ r₀) (hrHi : r₀ ≤ D/2+1)
    (hg : g ≠ 0) (hAp : IsApolar h r₀ hrD g)
    (hmin : ∀ k (hk : k ≤ D), k < r₀ →
      ∀ c : Fin(k+1) → ℂ, IsApolar h k hk c → c = 0) :
  ∃ z : ℂ, ∃ b : Fin(r₀+1) → ℂ, ∃ q : Polynomial ℂ,
    let h' := transformedMoments z h
    h' ≠ 0 ∧ b ≠ 0 ∧ IsApolar h' r₀ hrD b ∧
    b ⟨r₀, by omega⟩ = 1 ∧ q.Monic ∧ q.natDegree = r₀ ∧
    (∀ i : Fin(r₀+1), q.coeff i.val = b i) ∧
    (∀ k (hk : k ≤ D), k < r₀ →
      ∀ c : Fin(k+1) → ℂ, IsApolar h' k hk c → c = 0)
```

The proof may split the dehomogenization basis, last-coefficient identity, scalar normalization, and minimal-witness package into separately audited source modules. The output may pass `q`, `q.Monic`, `q.natDegree=r₀`, exact `q.coeff` correspondence, apolarity, and lower-kernel triviality directly to the conditional normalized quotient and Frobenius arguments. No premise that the original `h` already has a finite monic chart may be added. There is no assertion here that the original-coordinate Hankel middle rank equals `r₀`: mode transport and all-width equivalence remain unproved, as does `NLA.Statements.TR14.Target`.

## Source locks and review gate

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` (§2) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| Audited `GL2CoefficientBasis.lean` | `548b46a87516484b75022bd5d0d901132ab37762d4991ebb09eeec5b0f509a2f` |
| Audited `GL2MomentDual.lean` | `09d4126c2c3762fd15f13a026cca8aa085abcfd21bd32627396819bda4ab0de2` |
| Audited `GL2ApolarPairing.lean` | `81be7d13c6df0ef5e28e135f785c344498e4fc4dd88ab5f5963e38adf9681cb5` |
| Audited `GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| Approved `GL2_APOLAR_TRANSPORT_PRE_REVIEW.md` | `10e61abda0aa135eff2d561a43b918b25630867ba26e92bb83bd5d2fcc581f40` |
| Approved `GL2_APOLAR_TRANSPORT_INDEPENDENT_PRE_REVIEW.md` | `8d7c64bdef1741b9f1784b1a7889e742b82af064180e08ee11e29a0d3a011cf2` |

An independent mathematical review of **this exact document** is required before any Lean normalization source. After implementation, each frozen Lean source requires a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit before aggregate import. Changed contract or source bytes reopen the respective review.
