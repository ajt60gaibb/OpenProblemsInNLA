# TR-14 one-factor local Fourier decomposition: exact pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen for a separate mathematical review before Lean implementation. This is one local factor of the canonical `solution.tex` §3 construction. It leaves the factorization/CRT bridge, the global symmetric width, the other upper bound, the ordinary lower bound, and the frozen `NLA.Statements.TR14.Target` open.

## Mathematical assertion and exact coefficients

Let `m≥3`, `ℓ≥1`, `B_ℓ=ℂ[z]/(z^ℓ)`, and `Λ:B_ℓ→ₗ[ℂ]ℂ` satisfy the **genuine** Frobenius condition

\[
  \forall a\in B_\ell,\quad
  (\forall b\in B_\ell,\ \Lambda(ab)=0)\Longrightarrow a=0.
  \tag{ND}
\]

The audited local representation defines the unique `u∈B_ℓ` with
`Λ(a)=top_ℓ(ua)` for every `a`. The frozen `LocalUnitRoot.lean` proves from
(ND) that `u_0=Λ(z^{ℓ−1})≠0` and supplies `w∈B_ℓ` with `w^m=u`. Put

\[
 N=(m-1)(\ell-1)+1\ge1,
\]

choose a primitive `N`th root `ζ∈ℂ`, and let `R_ℓ:B_ℓ→ℂ[z]_{<ℓ}` be the
**canonical monic remainder** map. For each `j∈Fin N`, define the complex-linear
functional and its exact scalar

\[
 F_j(a)=R_\ell(wa)(\zeta^j),\qquad
 c_j=N^{-1}\big((\zeta^j)^{\ell-1}\big)^{-1}.
 \tag{LF}
\]

Evaluation is on the polynomial **representative** `R_ℓ(wa)`, not on a quotient
class at `ζ^j`. The same `F_j` is used in each of the `m` modes. For every
`a:Fin m→B_ℓ`, the required exact identity is

\[
 \Lambda\!\left(\prod_{k\in Fin m}a_k\right)
   =\sum_{j\in Fin N}c_j\prod_{k\in Fin m}F_j(a_k).
 \tag{LFD}
\]

There are exactly `N` indexed summands, including zero scalar contributions;
no minimal local rank is claimed. All coefficients are complex and **not
conjugated**. The inverse character in `c_j` agrees with the canonical
formula. Root existence does not introduce an analytic branch: the scalar
root and the nilpotent lift are finite algebraic choices.

## Proof obligations and no-loss coefficient bridge

For each mode set `P_k=R_ℓ(wa_k)`. Its support has exponents `<ℓ`. The
polynomial `P=∏_k P_k` has support in
`0,…,m(ℓ−1)` (also when a factor is zero). The quotient map sends
`P` to `∏_k(wa_k)=w^m∏_k a_k=u∏_k a_k`. Because `ℓ−1<ℓ`, the quotient's top
coefficient equals the **unreduced** polynomial coefficient `[z^{ℓ−1}]P`.
Consequently

\[
 \Lambda(\prod a_k)=[z^{\ell-1}]P.
\]

Polynomial evaluation is multiplicative, so
`P(ζ^j)=∏_kR_ℓ(wa_k)(ζ^j)=∏_kF_j(a_k)`.
The audited `primitive_fourier_coefficient_inv` applies to the exact vector
`k↦[z^k]P` on `Fin (m(ℓ−1)+1)` and yields (LFD). This step must prove the
full finite coefficient expansion of `P(ζ^j)`; an equality only on monomial
products is insufficient. Its exponent cutoff is exact: the next exponent
congruent to `ℓ−1` is `m(ℓ−1)+1`, one above the product bound.

The remainder map is complex-linear, multiplication by fixed `w` is
complex-linear, and polynomial evaluation at a fixed node is complex-linear.
Lean must exhibit `F_j : B_ℓ→ₗ[ℂ]ℂ`, rather than merely a pointwise function.
The proof must use the already audited exact `Fin ℓ` power basis and truncated
convolution; it may not assume a quotient evaluation homomorphism at a
nonzero root of unity.

## Relation to the frozen tensor target

For a root `α∈ℂ` of multiplicity `ℓ` and `n≥2`, the exact zero-based local
mode-class map is

\[
 M_\alpha(v)=\sum_{i\in Fin n}v_i(\alpha+z)^i\in B_\ell.
 \tag{MC}
\]

It is complex-linear for every `ℓ≥1`; **no** bound `ℓ≤n` is allowed. Define
`G_j=F_j∘M_α : (Fin n→ℂ)→ₗ[ℂ]ℂ` and the coordinate vector
`V_j(i)=G_j(e_i)`. Then `G_j(v)=∑_{i∈Fin n}V_j(i)v_i`, so (LFD) applied to
`a_k=M_α(v_k)` uses the same `V_j` in all modes. At `v_k=e_{i_k}` it has
the exact frozen zero-based tensor monomial `∏_kV_j(i_k)`, with no binomial
factor or conjugation.

This local identity is **not yet** a `SymmetricWidth` witness for the global
`Hankel h`. To obtain one, a later independently reviewed gate must construct
the actual CRT algebra equivalence of the least-apolar quotient, decompose
its Frobenius functional into local functionals, prove that the image of
`[p_v]` in each factor is (MC), sum (LFD) over all factors, and prove
`∑_aN_a=(m−1)r₀−(m−2)s`. The audited all-moment quotient pairing then
identifies that sum with every frozen Hankel coordinate. Finally the audited
GL₂ width transport returns to the original coordinates, including a root
initially at infinity. None of these dependencies is added as a hypothesis
to the final Target, which still quantifies over **all** `m≥3`, `n≥2`,
moments `h`, and widths `r`.

## Proposed narrow Lean boundaries

The following are sketches of exact signatures; names may differ but the
quantifiers and identities may not weaken.

```lean
def localFourierFunctional (m ℓ : ℕ) (hℓ : 0 < ℓ)
    (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) :
    LocalTruncated ℓ →ₗ[ℂ] ℂ :=
  -- a ↦ Polynomial.eval (ζ ^ j.val)
  --       (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow ℓ) (w * a))

theorem local_fourier_multilinear (m ℓ : ℕ)
    (hm : 3 ≤ m) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ)
    (hFrob : ∀ a, (∀ b, Λ (a * b) = 0) → a = 0) :
    ∃ w : LocalTruncated ℓ,
    ∃ ζ : ℂ,
      IsPrimitiveRoot ζ (localFourierCount m ℓ) ∧
      w ^ m = localFrobeniusElement ℓ hℓ Λ ∧
      ∀ a : Fin m → LocalTruncated ℓ,
        Λ (∏ k, a k) =
          ∑ j : Fin (localFourierCount m ℓ),
            (localFourierCount m ℓ : ℂ)⁻¹ *
              ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ *
              ∏ k, localFourierFunctional m ℓ hℓ w ζ j (a k)
```

The first gate may prove the representative-degree/evaluation lemmas and
the exact (LFD) in separate unimported modules. A later mode-vector lemma
should express (MC) as a linear map and prove its basis coordinates; a purely
set-theoretic existence of rank-one factors would be weaker than (LF).

## Endpoints and independent self-check

- `ℓ=1`: `z=0`, `N=1`, and `ζ=1`. Each representative is constant and
  (LFD) reads `Λ(∏a_k)=∏(wa_k)` with `w^m=u=Λ(1)`. There is no positive-degree
  coefficient step. This covers every `m≥3` required by the target.
- `ℓ=2,m=3`: `N=3`; the product of three degree-one representatives has
  degree at most `3`. The selected coefficient is degree `1`; the next
  congruent degree is `4` and cannot alias. The phase is `(ζ^j)^{-1}`.
- `ℓ=3,m=3`: `N=5`; the product degree is at most `6`, the selected degree
  is `2`, and the next congruent degree is `7`.
- `m=2` has the same cutoff arithmetic for every `ℓ≥1`, but the audited
  Fourier filter has the intentionally narrower `m≥3` signature matching
  TR-14. A new reviewed lemma would be needed to claim `m=2` in Lean.
- `m=1,ℓ=1` is a meaningful one-node scalar identity. For `m=1,ℓ>1`,
  `N=1` aliases all polynomial degrees, so (LFD) with (LF) is **false**.
  Example: `ℓ=2`, `Λ(a)=[z]a`, `u=w=1`, `a=1` gives `Λ(1)=0` but
  `R₂(w·1)(1)=1`. Thus the main claim does not include `m=1`; `m=0`
  also lies outside the construction.
- Zero moments have no Frobenius functional to which (ND) applies and are
  handled by the separately audited width-zero lemmas. Balanced
  middle-catalecticant kernels do not change the local calculation. The
  original-coordinate root at infinity is handled by chart transport before
  local decomposition.

## Exact source locks

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` §§2–3 | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `LocalFourierFilter.lean` | `2e128ccd73ab653c9356ba478159af1af6d3fd8e728dec15ead29efd3728daea` |
| Audited `LocalTopCoefficient.lean` | `0803a7a5c625b364527b4cbbcbba825d6dd410c81ef648018e18ee4f5cfc3275` |
| Frozen, pending independent final audit `LocalUnitRoot.lean` | `ce623be5bde47e2e60c5198c31ac3215ed061d7b2a8d7d278e415390f9b1dc28` |
| Audited `MomentQuotientModePairing.lean` | `24adc0f2e21ee8f84deb8ef4d6eddc8cc056327c2601e69f7c4a2a2cb35ae6cf` |
| Approved `LOCAL_FOURIER_UPPER_PRE_REVIEW.md` | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Approved `LOCAL_TOP_COEFFICIENT_PRE_REVIEW.md` | `c5797947009882f77bacc12d3a3f641178a38a6aa134ffc842aba9cb9ecab37b` |

An independent review must verify this **exact** document before Lean
implementation, especially the quotient-representative distinction, the
coefficient cutoff, the `m=1` exclusion, linear mode factors, and the lack of
an assumed CRT. Any changed bytes reopen that review. The canonical problem
ID, README, and frozen Target remain unchanged.
