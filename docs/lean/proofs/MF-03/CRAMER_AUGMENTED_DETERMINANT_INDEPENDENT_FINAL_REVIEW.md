# MF-03 Cramer numerator and augmented determinant: independent final review

**Disposition:** approved for aggregate import as an exact partial proof gate. Frozen source: `lean-statements/NLA/Proofs/MF03/CramerAugmentedDeterminant.lean`, SHA-256 `6a6bd97db8034b1a81dc11189d483bc39e6d55580889f2f00d41b2cc60ba94c6`. It implements the independently approved precontract SHA-256 `3e41367eb3e37a088d8a22fc6d874b1666c689159d2034f9430071fd005952f8` without altering the original MF-03 README, determinant definitions, or frozen Target.

The single public theorem has the exact approved all-order signature

```lean
theorem cosinePadeToeplitz_cramer_eq_augDet (m : ℕ) (c : Fin m) :
    (cosinePadeToeplitz m).cramer (cosinePadeRHS m) c =
      (-1 : ℝ) ^ (c.val + 1) * cosineAugDet m (c.val + 1)
```

I checked the proof's private matrix identity entrywise. The inverse `Fin.cycleRange c` permutation moves transposed Cramer row `c` to row zero, moves original rows below `c` down by one, and fixes rows above. The replaced row is exactly the negative first row of the **original infinite** `cosineAugDet m (c.val+1)`; the remaining rows have precisely its `r<c.val+1` shift, with natural subtraction matching the frozen definitions. `Matrix.det_permute`, `Fin.sign_cycleRange`, and the one negative row produce `(-1)^(c.val+1)`. There is no extra sign, normalization, denominator, finite cutoff, or tableau substitution. The proof covers `m=1`, first and last columns, and the vacuous `m=0` case by `Fin.elim0`.

I separately built `NLA.Proofs.MF03.CramerAugmentedDeterminant` with pinned Lean 4.33.1 (8,717 jobs) and imported it in `/private/tmp/mf03-cramer-augmented-determinant-independent-audit.lean` at SHA-256 `d77e0feef67fcc82d1b280b3bf3bce58fc5c218bcddba7d1001720ff76771457`. The imported file restates the exact signature as an `example` closed only by the public theorem; `#assert_trust kernel` passed and `#print axioms` showed only `[propext, Classical.choice, Quot.sound]`. A source search found no `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.

This is the Cramer numerator identity only. Forming the normalized Padé coefficients, proving the numerator/high-degree equations, reduction, disk estimate, and the full MF-03 Target remain separate obligations.
