# RA-10 constant-eleven arithmetic: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact conditional real-arithmetic gate for Lean implementation.

I reviewed `CONSTANT_ELEVEN_ARITHMETIC_PRE_REVIEW.md` at SHA-256 `1753e6adac3c596bd4d2ddb3ac675874c57a8f58bf810ea6399c6873c9a10433` against the locked RA-10 solution Equations (15)–(21) and frozen target. The source's one-based leading sum `i≤k` is the contract's zero-based `i<k`; the tail `i>k` is zero-based `i≥k`. The contract deliberately treats `F,τs,g,e,e₀,r,ε,τ` as real placeholders for the exact source quantities, without claiming the missing matrix identities.

Under `g≥0`, `r≤e`, and `e₀≤e+r`, the exact chain is `5e₀+r≤5e+6r≤11e`. Multiplication by `g` preserves order, so the stated excess premise yields `F−τs≤11ge`. This includes `g=0` and `e=0` without division. Under `g,ε≥0`, the next exact chain is `11ge≤11gετ≤11ετs`; hence `F≤(1+11ε)τs`. No positivity of `e`, `τ`, or `τs` is required for these conditional implications, and the literal constant `11` is retained.

Approval covers only these two conditional scalar implications. The full proof must still establish the matrix inequalities (15)–(18), the relation of the placeholders to frozen norms and truncations, the positive-tail comparison, and the operator-monotone integral transfer. Freeze any Lean implementation for an independent imported exact-signature/LeanCert kernel audit before aggregate import.
