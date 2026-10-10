# TR-14 local top-coefficient Frobenius algebra: exact pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen for independent mathematical review before Lean implementation. This is the next local-algebra dependency of the approved TR-14 local Fourier upper construction. It does not construct the CRT, assert that a global Frobenius functional has local components, or claim a width or the frozen Target.

## Exact local algebra and coefficients

For every integer `ℓ≥1`, set `B_ℓ=ℂ[z]/(z^ℓ)`, represented in Lean by `AdjoinRoot ((Polynomial.X : Polynomial ℂ)^ℓ)`, and let `z` be its quotient root. The monic power basis has the **exact** indices `Fin ℓ`:

\[
 z^\ell=0,\quad z^{\ell-1}\ne0,\quad
 a=\sum_{j=0}^{\ell-1}a_jz^j
 \quad\text{uniquely for every }a\in B_\ell.
\]

Define `coeff_ℓ(a,j)=a_j` by that basis and `top_ℓ(a)=coeff_ℓ(a,ℓ−1)`. For every `j<ℓ`, `coeff_ℓ(z^k,j)=1` when `j=k<ℓ` and zero otherwise. Multiplication has the exact truncated convolution

\[
 \operatorname{coeff}_\ell(ab,j)
  =\sum_{i=0}^{j}\operatorname{coeff}_\ell(a,i)
                    \operatorname{coeff}_\ell(b,j-i)
 \qquad(0\le j<\ell).
 \tag{TC}
\]

Terms of total degree at least `ℓ` vanish **in the quotient**, while (TC) includes every term of degree `j<ℓ`. No analytic approximation or numerical tolerance is involved.

## Exact Frobenius representation

For any complex-linear `Λ:B_ℓ→ₗ[ℂ]ℂ`, define

\[
 u_j=\Lambda(z^{\ell-1-j})\quad(0\le j<\ell),
 \qquad u=\sum_{j=0}^{\ell-1}u_jz^j.
 \tag{U}
\]

Then for **every** `a∈B_ℓ`,

\[
 \Lambda(a)=\operatorname{top}_\ell(ua).
 \tag{F}
\]

The representation element `u` is unique. In particular, its constant coefficient is **exactly**

\[
 u_0=\Lambda(z^{\ell-1}).
 \tag{C}
\]

Assume the genuine local Frobenius condition

\[
 \forall a\in B_\ell,\quad
   (\forall b\in B_\ell,\ \Lambda(ab)=0)\Longrightarrow a=0.
 \tag{ND}
\]

Then `u₀≠0`. Indeed, if `Λ(z^{ℓ−1})=0`, every `z^{ℓ−1}b` is `coeff_ℓ(b,0) z^{ℓ−1}`, so `z^{ℓ−1}` would be a nonzero radical element. This argument includes `ℓ=1`: `z⁰=1`, and (ND) forces `Λ(1)≠0`. The resulting `u` is a unit, since an element of `B_ℓ` is invertible when its constant coefficient is nonzero. The first Lean gate may prove (TC), (U), (F), uniqueness, and (C) before the Frobenius-to-nonzero and unit consequences; no statement may silently assume `u₀≠0` without (ND) or an explicit hypothesis.

## Exact finite root of a local unit

For every `m≥1` and every `u∈B_ℓ` with `u₀≠0`, there is `w∈B_ℓ` with

\[
 w^m=u.
 \tag{R}
\]

This is a finite algebraic construction. Choose `ρ∈ℂ` with `ρ^m=u₀`, available because `ℂ` is algebraically closed; `ρ≠0`. Put `w₀=ρ`. For `1≤j<ℓ`, suppose `w₀,…,w_{j-1}` are selected and set `W_{<j}(z)=∑_{i<j}w_i z^i`. The degree-`j` coefficient of `(W_{<j}+w_jz^j)^m` is

\[
  R_j+m\rho^{m-1}w_j,
  \qquad R_j=[z^j]W_{<j}(z)^m.
\]

No term containing two `w_j z^j` factors can affect degree `j`, and the other `m−1` factors contribute only `ρ` to the term with one such factor. Since `mρ^{m−1}≠0` in `ℂ`, choose

\[
 w_j=(u_j-R_j)/(m\rho^{m-1}).
 \tag{REC}
\]

After exactly `ℓ−1` steps, equality of the `Fin ℓ` coefficients proves (R) in `B_ℓ`. The final TR-14 construction uses `m≥3`, but this local theorem is valid for every positive `m`; `m=0` is deliberately excluded. There is no need to choose a global analytic branch of a complex root or use an infinite binomial series.

## Proposed Lean boundaries

These are signature sketches. Routine transports between `Fin ℓ` and the monic `AdjoinRoot.powerBasis'` index may be explicit in source; they must not change the claims.

```lean
abbrev LocalTruncated (ℓ : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial ℂ) ^ ℓ)

def localCoeff (ℓ : ℕ) (hℓ : 0 < ℓ)
    (a : LocalTruncated ℓ) (j : Fin ℓ) : ℂ :=
  -- coordinate from the monic power basis

def localTopCoeff (ℓ : ℕ) (hℓ : 0 < ℓ)
    (a : LocalTruncated ℓ) : ℂ :=
  localCoeff ℓ hℓ a ⟨ℓ - 1, by omega⟩

def localFrobeniusElement (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) : LocalTruncated ℓ :=
  ∑ j : Fin ℓ,
    (Λ ((AdjoinRoot.root ((Polynomial.X : Polynomial ℂ)^ℓ)) ^ (ℓ - 1 - j.val))) •
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℂ)^ℓ)) ^ j.val

theorem localFrobenius_repr (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) (a : LocalTruncated ℓ) :
    Λ a = localTopCoeff ℓ hℓ (localFrobeniusElement ℓ hℓ Λ * a)

theorem localFrobenius_unique ... :
    (∀ a, Λ a = localTopCoeff ℓ hℓ (u * a)) →
    u = localFrobeniusElement ℓ hℓ Λ

theorem localFrobenius_const_ne_zero ...
    (hFrob : ∀ a, (∀ b, Λ (a * b) = 0) → a = 0) :
    localCoeff ℓ hℓ (localFrobeniusElement ℓ hℓ Λ) ⟨0, hℓ⟩ ≠ 0

theorem local_unit_has_nth_root (ℓ m : ℕ)
    (hℓ : 0 < ℓ) (hm : 0 < m) (u : LocalTruncated ℓ)
    (hu0 : localCoeff ℓ hℓ u ⟨0, hℓ⟩ ≠ 0) :
    ∃ w : LocalTruncated ℓ, w ^ m = u
```

The implementation must prove the power-basis expansion and (TC) before relying on coefficient comparison. The root theorem may instead use an equivalent **finite** nilpotent binomial polynomial, but the resulting statement must retain `ℓ≥1`, `m≥1`, exact equality (R), and no additional analytic or local-genericity assumptions. Separate unimported Lean modules and independent source audits are acceptable for the representation and root stages.

## Endpoint and numerical self-check

- `ℓ=1`: `B₁≃ℂ`, `z=0`, `u=Λ(1)·1`, (F) says `Λ(a)=Λ(1)a`; (ND) gives `Λ(1)≠0`, and one scalar `m`th root proves (R). There are zero positive-degree recursion steps.
- `ℓ=2`: `u=u₀+u₁z`, with `u₀=Λ(z)`, `u₁=Λ(1)`. For `a=a₀+a₁z`, (F) reads `Λ(a)=u₁a₀+u₀a₁`. The Frobenius matrix has determinant `−u₀²`; its nondegeneracy forces `u₀≠0`. Given `ρ^m=u₀`, `w₁=u₁/(mρ^{m−1})`.
- `m=3,ℓ=3`: after `ρ³=u₀`, `w₁=u₁/(3ρ²)` and `w₂=(u₂−3ρw₁²)/(3ρ²)`. Then `(ρ+w₁z+w₂z²)^3=u₀+u₁z+u₂z²` modulo `z³`.
- The local multiplicity `ℓ` may exceed the mode dimension `n`; no assumption `ℓ≤n` is valid or used. A root at infinity is handled by the separately audited GL₂ chart normalization, **before** any local algebra is chosen. Balanced middle-catalecticant cases do not alter (TC)–(R). Zero moments have no Frobenius functional to which (ND) applies.

## Exact source locks

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` §§2–3 | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| Audited `lean-statements/NLA/Proofs/TR14/MomentQuotientModePairing.lean` | `24adc0f2e21ee8f84deb8ef4d6eddc8cc056327c2601e69f7c4a2a2cb35ae6cf` |
| Audited `lean-statements/NLA/Proofs/TR14/LocalFourierFilter.lean` | `2e128ccd73ab653c9356ba478159af1af6d3fd8e728dec15ead29efd3728daea` |
| Approved `docs/lean/proofs/TR-14/LOCAL_FOURIER_UPPER_PRE_REVIEW.md` | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Independent `LOCAL_FOURIER_UPPER_INDEPENDENT_PRE_REVIEW.md` | `e335efd8707352413d9219464730f89aa882f6059c9aead7624a79cb3132c248` |
| Approved `MOMENT_QUOTIENT_MODE_PAIRING_PRE_REVIEW.md` | `d9c791805617767bc2cf2d933a9d83ed9b188c6f6de614ee7f697d5d93d4f114` |
| Independent `MOMENT_QUOTIENT_MODE_PAIRING_INDEPENDENT_PRE_REVIEW.md` | `b87a65c54a92457396cade54c183d7f0a0f79f1e869c9610e9883a2d130a69b9` |
| Final `MOMENT_QUOTIENT_MODE_PAIRING_INDEPENDENT_FINAL_REVIEW.md` | `6c16b242fff13f996799f0dafe10360d6c7781c9ae678994e83f063d2730fad2` |

An independent review must verify this **exact** contract, especially the reversed indices in (U), `ℓ=1`, the Frobenius implication, and the nonzero recursion denominator, before any Lean implementation. Changed bytes reopen that review. The canonical problem ID, README, and frozen Target remain unchanged.
