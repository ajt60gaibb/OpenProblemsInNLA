# MF-03 numerator polynomial: independent final review

**Disposition:** approved for aggregate import as an exact partial gate. Frozen source `lean-statements/NLA/Proofs/MF03/PadeNumeratorPolynomial.lean` has SHA-256 `fff4c3b1e3ca85865ef15f404101d581af0bdfc638c38a22854da61bde4538f5`; it implements the numerator stage of the independently approved all-order polynomial contract SHA-256 `a9da6d70ba2c4c8fc968955e78d2041eb7809ad843729970f1be8f3496bf1f0c`.

I checked the public literal polynomial: for every `n≤m`, it places the **frozen** finite convolution `Σ_{i<n+1} (cosinePadeDenominator m).coeff i / (2(n−i))!` at `X^n`, with no changed denominator or factorial. Distinct monomials give that exact coefficient; all coefficients above `m` are zero, hence `natDegree≤m`. At `m=0`, the single coefficient is the expected constant `1`. This stage does not assert any high-degree Padé equation.

I independently built `NLA.Proofs.MF03.PadeNumeratorPolynomial` with pinned Lean 4.33.1 (8,766 jobs). The separate imported audit `/private/tmp/mf03-pade-numerator-polynomial-independent-audit.lean` at SHA-256 `38c390aa9804022290f812deb5a52ea0ac14ea1c9fb3795eb4706f14a07efd18` restates the exact definition and all three public theorem signatures. It passed `#assert_trust kernel` on the definition and all three theorems; the final degree theorem reports only `[propext, Classical.choice, Quot.sound]`. Source scan found no `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.

The high-degree equations, full normalized pair, complex coefficient bound, reduction, disk estimate, and frozen MF-03 Target remain separate obligations.
