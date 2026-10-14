# TR-14 quotient and Frobenius pairing: exact pre-proof contract

**Author:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Status:** frozen mathematical and proposed Lean contract for independent review **before** implementation. It continues the audited `ApolarMinimal.lean` and the canonical proof's §2. It is a partial foundation, not `NLA.Statements.TR14.Target`.

## Input and the chart obligation

Fix `m≥3`, `n≥2`, `q=n−1`, `D=mq`, and a **nonzero** moment vector `h : Fin(D+1)→ℂ`. The audited minimal-apolar theorem supplies `1≤r₀≤⌊D/2⌋+1`, a nonzero homogeneous vector `G∈I_{r₀}`, and `I_d=0` for every `d<r₀`. Here `I_d` is the **exact** convolution kernel, not a generic, squarefree, or Vandermonde condition. The zero moment vector is handled separately through `MomentIndex.hankel_eq_zero_iff` and width-zero semantics. The final target's width `r` is unrelated to `r₀`.

The chosen `G(X,Y)=∑_{i=0}^{r₀}g_iX^{r₀−i}Y^i` may have `g_{r₀}=0`, a root at infinity. The affine quotient `ℂ[t]/(g(t))` of dimension `r₀` is therefore **not** available for the original coordinates without an additional step. The development must prove one of these equivalent routes:

1. **Chart normalization.** Choose `T∈GL₂(ℂ)` such that the transformed nonzero form `G'=φ_T G` has `G'(0,1)≠0`, then scale it to make `g'(t)=G'(1,t)` monic of degree exactly `r₀`. This is possible because a nonzero binary form cannot vanish on every projective direction. Define the transformed degree-`D` moment functional by `L'_D=L_D∘φ_T⁻¹`, where `φ_T` is substitution by `T` on homogeneous forms. Prove the exact pairing identity `L'_D((φ_TG)(φ_TQ))=L_D(GQ)` for every degree-`D−r₀` form `Q`; hence all apolar kernels, their dimensions, and minimal degree are carried by invertible maps. Define `h'_j=L'_D(X^{D−j}Y^j)`; prove the induced action on each degree-`q` mode is invertible and that the original and transformed Hankel multilinear forms are related by that action in **each** of the `m` modes. The later rank proof also needs this rank-preserving bridge.
2. **Coordinate-free equivalent.** Construct a degree-`r₀` finite algebra and Frobenius functional directly from the homogeneous quotient, with an explicit isomorphism to the normalized affine construction after a chart is chosen. It must deliver the same all-moment and mode-product identities and the original-coordinate middle-rank bridge. Merely assuming `g_{r₀}≠0` in a public all-`h` theorem is not this route.

The first route is the canonical source's route. `φ_T` and the dual action on `L_D` must be paired as displayed; transforming the polynomial without transforming the moment functional would invalidate apolarity. No conjugation occurs. The coordinate change must not become an extra premise of `NLA.Statements.TR14.Target`.

## Normalized affine quotient theorem

The main conditional lemma should be proved for a normalized vector `h'` and a monic affine polynomial

\[
 g(t)=t^{r₀}+\sum_{i=0}^{r₀-1}g_i t^i,
 \qquad A_g=\mathbb C[t]/(g),\quad \bar t=[t].
\]

Assume **exactly** that `g` is a degree-`r₀` nonzero apolar vector for `h'`, `r₀≤D`, and no smaller degree has a nonzero apolar vector. The apolar equation at every shift is the recurrence

\[
 h'_{j+r₀}+\sum_{i=0}^{r₀-1}g_i h'_{j+i}=0,
 \qquad 0\le j\le D-r₀.
\]

No recurrence beyond `D-r₀` is assumed for the input moments. Define the unique complex-linear `λ:A_g→ℂ` by `λ(\bar t^j)=h'_j` for `0≤j<r₀`, using the monic remainder basis. Induct using the displayed recurrence to prove the **full** match

\[
 \lambda(\bar t^j)=h'_j\qquad(0\le j\le D).
\]

The first new case is `j=r₀` (shift zero), and the final one is `j=D` (shift `D-r₀`); both must be present. For the balanced case `D=2r₀−2`, the available shifts are exactly `0,…,r₀−2`, which still suffice. For `r₀=1`, the basis is `{1}`, the recurrence starts at shift zero, and no empty-sum or degree-zero quotient shortcut may drop `h'_D`. The quotient has complex dimension **exactly** `r₀`.

The bilinear pairing `(a,b)↦λ(ab)` must be nondegenerate in the precise Frobenius sense

```lean
∀ a : A_g, (∀ b : A_g, λ (a * b) = 0) → a = 0
```

and not merely `λ≠0` or nondegeneracy on a selected basis. Let `J={a : ∀b, λ(ab)=0}`. Prove it is an ideal. If `J≠0`, the ideal correspondence for the principal quotient gives `A_g/J≅ℂ[t]/(g')` for a monic **proper** divisor `g'|g`, with `r' = deg g' < r₀`. Because `λ(J)=0`, it descends. Thus `λ(\bar t^j g'(\bar t))=0` for every `j≥0`; for `0≤j≤D-r'`, the all-moment match converts this to the exact `r'`-degree apolar equations. This contradicts minimality. The possible `r'=0` would force all moments to zero, contradicting `h'≠0`. Therefore `J=0`. This proof may use a different verified ideal/linear-algebra lemma but must not assume the pairing is Frobenius.

For arbitrary mode polynomials `p₁,…,p_m` of degree at most `q`, their product has degree at most `D`. By the all-moment match and linearity, prove the exact identity

\[
 H_{h'}(p₁,\ldots,p_m)
   =L'_D(p₁\cdots p_m)
   =\lambda([p₁]\cdots[p_m]).
\]

Here the first expression extends the frozen coordinate tensor multilinearly; check the zero-based `Fin n` basis and all products through degree `D`. A statement matching only `h'_0,…,h'_{r₀−1}` is insufficient for this bridge.

## Proposed Lean boundaries

The following are signature sketches; quotient and homogeneous-form APIs may differ, but the public assertions must be equivalent:

```lean
normalized_moment_quotient
    (hh : h' ≠ 0) (hr : 1 ≤ r₀) (hrD : r₀ ≤ D)
    (hgTop : g ⟨r₀, by omega⟩ = 1)
    (hgApolar : IsApolar h' r₀ hrD g)
    (hmin : ∀ d < r₀, ∀ b, IsApolar h' d ... b → b = 0) :
  ∃ λ : A_g →ₗ[ℂ] ℂ,
    Module.finrank ℂ A_g = r₀ ∧
    (∀ j : Fin (D + 1), λ (tbar ^ j.val) = h' j) ∧
    Frobenius A_g λ

apolar_normalized_chart
    (hh : h ≠ 0) (hG : G ≠ 0) (hGApolar : IsApolar h r₀ ... G) :
  ∃ T : GL₂(ℂ), ∃ h' G',
    G' = φ_T G ∧ G'_{r₀} ≠ 0 ∧
    (∀ d ≤ D, φ_T (I_d(h)) = I_d(h')) ∧
    (induced degree-q mode map is invertible) ∧
    (the two Hankel multilinear forms are related in all m modes)
```

The `...` marks dependent proof arguments in this sketch, **not** mathematical assumptions. A normalized quotient theorem may be implemented first and reviewed as conditional progress, but the global `h` route must discharge the chart obligation before it is used to prove original-coordinate middle rank or any width statement. Both routes retain exceptional, repeated-root, and balanced cases; neither asks for normality, positivity, or numerical computation.

## Scope and source locks

The middle catalecticant rank equality and the balanced dimension of `I_{r₀}` are subsequent §2 gates: pull back the Frobenius pairing through the two polynomial truncation surjections and transport the rank through the chosen `GL₂` chart. Local CRT factors and the arbitrary ordinary-decomposition lower bound come later. No quotient or chart lemma alone proves the unchanged all-width equality.

| Reviewed input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Proof `tensor-computations/TR-14/solution.tex` (§2) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Approved `MOMENT_ALGEBRA_PRE_REVIEW.md` | `2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840` |
| Approved `APOLAR_MINIMAL_PRE_REVIEW.md` | `93908b1804fdd4f2504382e59a6a2b2d50b5544e5c139d37ace3f530b30a4b23` |
| Frozen `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |

Independent mathematical review of this contract is required before quotient or chart implementation. Every later source freeze requires exact-signature, imported LeanCert kernel, proof-escape, and axiom reviews. Do not claim a full TR-14 proof from a conditional normalized quotient lemma.
