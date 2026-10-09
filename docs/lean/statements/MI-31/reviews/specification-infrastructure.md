# MI-31 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the MI-31 specification or its canonical page. Phase: `specification`. Verdict: **APPROVE** for Lean statement implementation. This is an exact-statement review, not a proof audit or external human peer review.

## Reviewed inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `matrix-inequalities-and-norms/MI-31/README.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/ORIGINAL.md` | `9d49717605baf2379896f6360417092c70bb74773120002cd5f4c15950a04093` |
| `docs/lean/statements/MI-31/NUMERICAL_TARGETS.md` | `e1d5dc6fdb06b16cbcf95d2a648f435d4cdd8bcefd2a0e13034e0cfe93556b76` |

The retained original and canonical README are byte identical. The permanent ID and canonical path remain unchanged.

## Exact mathematical comparison

The canonical statement quantifies **one absolute positive constant** before every positive rectangular dimension pair, every real exponent `1 ≤ p ≤ 2`, every extended exponent `2 ≤ q ≤ ∞`, and every real matrix profile. The specification keeps this order, so the constant cannot depend on dimensions, exponents, or the profile. It includes the one-row and one-column cases and all four parameter endpoints.

The input law is one independent standard real `N(0,1)` Gaussian at each matrix coordinate, multiplied by that coordinate's deterministic real profile entry. The vector norms and induced `p→q` norm are the ordinary finite-dimensional real norms, with the `∞` norm as the coordinate maximum. The specification correctly treats `p*=∞` when `p=1` and uses the exact finite formula `p/(p−1)` otherwise. It also applies `min(∞,L(k))=L(k)` for the capped logarithmic factors, with `L(k)=max(1,ln k)`.

The deterministic `D₁` is the maximum of input-dual row norms, and `D₂` is the maximum of output column norms. Only the entrywise maximum `Z` is inside its Gaussian expectation. The left-hand expectation is that of the genuine induced norm of the same random matrix. The three terms occur with the original square-root caps and plus signs. The target is only the weak upper inequality; the original expressly makes no matching lower-bound claim with the same terms. No boundedness, rank, normalization, variance-profile restriction, or fixed-exponent hypothesis has been added.

The page's `Solved` notice incorporates an informal audit and an entropy-cardinality convention correction to a candidate proof. The specification preserves that notice in `ORIGINAL.md` without modifying the mathematical inequality. I found no missing quantifier, endpoint, constant, expectation placement, or numerical convention.
