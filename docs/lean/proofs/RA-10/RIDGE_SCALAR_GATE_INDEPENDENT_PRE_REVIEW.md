# RA-10 ridge scalar gate: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact scalar identities and finite-tail comparison for Lean implementation.

I reviewed `RIDGE_SCALAR_GATE_PRE_REVIEW.md` at SHA-256 `325fc8c9a9e32c35aec0e29d04b770891094bb9477e868697833e337dbc122e7` against the locked canonical README, solution, frozen RA-10 statement, and overarching constant-eleven contract. The solution's Equation (12) is exactly `|a/(s+a)-b/(s+b)| = s|a-b|/((s+a)(s+b)) ≤ |a-b|/(s+c)` for `s,c>0`, `a≥c`, `b≥0`. All denominators are positive; `(s+a)(s+b)≥s(s+c)`, so the coefficient is exactly `1/(s+c)`. The equality and bound cover `a=b`, `b=0`, and `a=c` without a strict spectral gap.

For `0≤x≤c`, positivity and `s+x≤s+c` give `x/(s+c)≤x/(s+x)`. Summing over the literal finite set `{i : Fin n | k≤i.val}` yields Equation (20), including an empty tail. In the source's one-based indices `i>k` is exactly this zero-based condition. The local hypotheses `a_i≤c` and `c>0` are justified only later from the frozen antitone spectrum and the positive-tail branch; they are not added to the final target. The public `ridgeAtom` must remain definitionally `x/(s+x)`, and the exact coefficient and filtered index set must be retained.

Approval is confined to these real scalar gates. Matrix resolvent, nuclear-norm perturbation, positive-integral representation, `TransferBound 11`, and the frozen RA-10 `Target` remain separate obligations. Freeze the Lean source after implementation for an independent imported exact-signature and LeanCert kernel audit before aggregate import.
