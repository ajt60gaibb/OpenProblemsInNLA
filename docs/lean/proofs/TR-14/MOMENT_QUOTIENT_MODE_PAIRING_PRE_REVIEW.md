# TR-14 moment-to-quotient mode pairing: exact pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen for a separate mathematical review before Lean implementation. This is one narrow gate in the independently approved local Fourier upper construction. It makes no symmetric-width, CRT, Frobenius, lower-bound, or full `NLA.Statements.TR14.Target` claim.

## Exact claim

Keep the frozen zero-based conventions. For natural `m,q`, put `D=m*q`, let `h : Fin (D+1) → ℂ`, let `g : Polynomial ℂ`, and let `Λ : AdjoinRoot g →ₗ[ℂ] ℂ`. Write `τ=AdjoinRoot.root g`. Assume the **all-degree** moment identity

\[
  \Lambda(\tau^j)=h_j\qquad(0\le j\le D).
\]

For every mode vector `v : Fin (q+1) → ℂ`, define the genuine affine mode polynomial and its quotient image by

\[
 p_v(t)=\sum_{a=0}^{q}v_a t^a,
 \qquad
 P_g(v)=p_v(\tau)=\sum_{a=0}^{q}v_a\tau^a.
\]

There are no binomial or factorial factors. For **every** `u : Fin m → Fin (q+1) → ℂ`, the gate proves the exact multilinear equality

\[
 \Lambda\!\left(\prod_{k=0}^{m-1}P_g(u_k)\right)
 =\sum_{i\in(\mathrm{Fin}(q+1))^{\mathrm{Fin}(m)}}
       h_{\sum_k i_k}\prod_{k=0}^{m-1}u_k(i_k)
 =\sum_i (\operatorname{Hankel}h)_i\prod_k u_k(i_k).
 \tag{MQ}
\]

Each monomial degree is `∑ₖ iₖ≤m*q=D`, so the assumed identity covers **every** summand, including the maximum degree. This works even if `g.natDegree` is smaller than `D`: multiplication and reduction happen inside `AdjoinRoot g`, while the supplied all-moment identity evaluates the resulting powers. A statement matching only the initial `g.natDegree` moments would be insufficient.

For the actual normalized least-apolar chart, use the audited `NormalizedQuotient.quotientMomentFunctional_all` to discharge the all-degree premise. The proposed corollary assumes precisely `g.Monic`, `g.natDegree≤D`, and `MonicMomentRecurrence h g`. A second corollary may replace the recurrence with the exact `IsApolar` hypothesis through audited `monicMomentRecurrence_of_apolar`; it must retain the exact degree and `Fin` types. Frobenius nondegeneracy and minimality are **not** needed for this gate, though the later local interpolation construction uses them.

## Proposed Lean boundaries

These are signature sketches; elaboration details may change while preserving the displayed formulas.

```lean
def affineModePolynomial (q : ℕ) (v : Fin (q + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (q + 1), Polynomial.C (v i) * Polynomial.X ^ i.val

def quotientMode (g : Polynomial ℂ) (q : ℕ)
    (v : Fin (q + 1) → ℂ) : AdjoinRoot g :=
  ∑ i : Fin (q + 1), (v i) • (AdjoinRoot.root g) ^ i.val

theorem quotientMode_eq_aeval (g : Polynomial ℂ) (q : ℕ)
    (v : Fin (q + 1) → ℂ) :
    quotientMode g q v =
      Polynomial.aeval (AdjoinRoot.root g) (affineModePolynomial q v)

theorem quotient_mode_pairing_of_all_moments {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ)
    (hall : ∀ j : Fin (m * q + 1),
      Λ ((AdjoinRoot.root g) ^ j.val) = h j)
    (u : Fin m → Fin (q + 1) → ℂ) :
    Λ (∏ k : Fin m, quotientMode g q (u k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k)

theorem quotientMomentFunctional_mode_pairing {m q : ℕ}
    (h : Fin (m * q + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ m * q)
    (hrec : MonicMomentRecurrence h g)
    (u : Fin m → Fin (q + 1) → ℂ) :
    quotientMomentFunctional h g hg hrD
      (∏ k : Fin m, quotientMode g q (u k)) =
      ∑ i : Fin m → Fin (q + 1),
        Hankel h i * ∏ k : Fin m, u k (i k)
```

`HankelIndex i` is exactly the `Fin (m*q+1)` index of `∑ₖ(iₖ).val`; the proof must use its bound, not introduce a different index or shift by one. The product-of-sums expansion is indexed by **all** functions `Fin m → Fin(q+1)` once, and commutativity in `AdjoinRoot g` gives `∏ₖτ^{iₖ}=τ^{∑ₖ iₖ}`. Linearity of `Λ` then gives (MQ) directly. The polynomial/evaluation lemma ensures `quotientMode` is truly the class of the canonical affine polynomial, not an unrelated coordinate encoding.

## Endpoints and independent self-check

- `m=0`: `D=0`; both products are empty products `1`, the multi-index type has one element, and (MQ) is exactly `Λ(1)=h₀`. The general gate need not assume `m≥3`.
- `q=0`: every mode has only index `0`; both sides equal `h₀∏ₖuₖ(0)` for every `m`, including `m=0`.
- `m=3,q=1`, index tuple `(0,1,1)`: the term is `h₂u₀(0)u₁(1)u₂(1)`; tuple `(1,1,1)` reaches `h₃=h_D`.
- `m=3,q=2`, tuple `(2,2,2)` reaches `h₆=h_D`; no top-degree term may be dropped by quotient reduction.
- The normalized least-apolar polynomial can have degree `r₀>q+1` in some target instances; (MQ) imposes no false `r₀≤n` premise. Balanced `D=2r₀-2` likewise requires no special case.
- The gate neither evaluates a quotient class at a complex Fourier node nor assumes any local factorization; those belong to later stages.

## Exact source locks

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` §§1–3 | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `lean-statements/NLA/Proofs/TR14/GL2HankelMode.lean` | `5b700ce0fbd05cfa39f047830b6455dc64cc361acfe3218f667d2af9f09e02c2` |
| Audited `lean-statements/NLA/Proofs/TR14/LocalFourierFilter.lean` | `2e128ccd73ab653c9356ba478159af1af6d3fd8e728dec15ead29efd3728daea` |
| Approved `docs/lean/proofs/TR-14/LOCAL_FOURIER_UPPER_PRE_REVIEW.md` | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Independent approval `LOCAL_FOURIER_UPPER_INDEPENDENT_PRE_REVIEW.md` | `e335efd8707352413d9219464730f89aa882f6059c9aead7624a79cb3132c248` |

An independent mathematical review of this exact document is required before implementing the gate. Changes to this document after the review reopen that obligation. The original TR-14 README, frozen Target, and existing problem ID remain unchanged.
