# MF-03 complex denominator tail: independent final review

**Disposition:** approved for aggregate import as an exact partial gate. Frozen source `lean-statements/NLA/Proofs/MF03/PadeDenominatorTail.lean` has SHA-256 `98bb11fc969f6d494556e32a1b72de59cadab82643643a43da9d528559c33277`, under the independently approved all-order polynomial contract SHA-256 `a9da6d70ba2c4c8fc968955e78d2041eb7809ad843729970f1be8f3496bf1f0c`.

The single public theorem has precisely the existing large-order disk gate's coefficient premise: for every `m,j` with `1≤j≤m`, `‖(cosinePadeDenominator m).coeff j‖≤(cosineTail m)^j`. I checked the proof's `c:Fin m` construction from zero-based `j−1`, its equality `c.val+1=j`, the literal denominator coefficient theorem, and `Complex.norm_real`/`Real.norm_eq_abs` transfer of the audited **coefficient-one** real bound. The denominator, tail, exponent, and threshold are unchanged. At `m=0` the quantified range is empty; first and last nonconstant coefficients are included for positive `m`.

I independently built `NLA.Proofs.MF03.PadeDenominatorTail` with pinned Lean 4.33.1 (8,766 jobs). The separate imported audit `/private/tmp/mf03-pade-denominator-tail-independent-audit.lean` at SHA-256 `aece755ed29a31b333aa60205a9139b5eab381b19c87732c8aeb6116f06f6d85` restates the exact theorem and passed `#assert_trust kernel`; reported axioms are only `[propext, Classical.choice, Quot.sound]`. Source scan found no `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.

The full normalized pair, disk estimate, reduction, and frozen MF-03 Target remain separate obligations.
