# MF-03 denominator polynomial: independent final review

**Disposition:** approved for aggregate import as an exact partial gate. The frozen source `lean-statements/NLA/Proofs/MF03/PadeDenominatorPolynomial.lean` has SHA-256 `ac24cd2160135b687225b9b9e75a0ca2f7963b13d67ba1b788d7b3f5afc32679`. It is the denominator construction stage of the independently approved all-order polynomial contract SHA-256 `a9da6d70ba2c4c8fc968955e78d2041eb7809ad843729970f1be8f3496bf1f0c`.

I checked the literal public definition `C 1 + ∑ c:Fin m, C((cosinePadeNonconstantCoeff m c:ℂ)) * X^(c.val+1)`. The constant coefficient is exactly `1`, the coefficient at each distinct one-based degree `c.val+1` is exactly the original determinant/Cramer coefficient, every coefficient above `m` is zero, and `natDegree≤m`. The proof uses all `c : Fin m`, so it covers the first and last nonconstant coefficients; for `m=0`, the sum is empty and the polynomial is `1`. It does not replace the denominator or assume a normalized Padé pair.

I independently built `NLA.Proofs.MF03.PadeDenominatorPolynomial` with pinned Lean 4.33.1 (8,765 jobs). The imported audit `/private/tmp/mf03-pade-denominator-polynomial-independent-audit.lean` at SHA-256 `9988a4437fa4534c235342444506ea43aa6b917e9fdc9bc887707de2c8ab58ce` restates the exact definition and all four public theorem signatures. It passed `#assert_trust kernel` on the definition and all four theorems; the final theorem reports only `[propext, Classical.choice, Quot.sound]`. Source scan found no `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.

The numerator, high-degree Padé equations, complex coefficient bound, reduction, disk estimate, and full Target remain separate obligations.
