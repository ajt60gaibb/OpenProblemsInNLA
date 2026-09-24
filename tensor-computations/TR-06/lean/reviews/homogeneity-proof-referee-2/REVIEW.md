# Independent Homogeneity proof review

Reviewer: `/root/tr06_statement_referee_2`, independent of the root proof author. Verdict: **approve these supporting lemmas at the inspected hash**.

Inspected source: `/private/tmp/tr06-proof-root/NLA/TR06/Homogeneity.lean`; preserved snapshot `NLA/TR06/Homogeneity.lean`; SHA-256 `689a6a46677c322b0070426f07a66c651ac55154927c9a6080f46d27ddd23ff1`.

## Exactness and proof logic

The final statement is the exact frozen extended angular-slope definition, evaluated at `t • A`, and equates it with `angularSlope r A / ENNReal.ofReal t` under precisely `0 < d` and `0 < t`. It makes no identifiability, regularity, or finiteness assumption on A or its slope. This is stronger than its use on the canonical locus but does not change the canonical target.

Scaling is implemented by absorbing the scalar into mode zero of an actual pure-factor tuple. The positive-order hypothesis is necessary for that construction and is present; no tensor-rank predicate is substituted. Nonzero scaling preserves every summand, maps reconstructed sums, and has an actual inverse scalar. This proves existence of each fixed decomposition length, exact rank including every shorter exclusion, and uniqueness up to the original finite permutation action.

Positive common scaling cancels in each normalized tensor coordinate without requiring nonzero input to the normalization identity. For actual decompositions the original nonzero conditions are retained. Both infimum inequalities are established by explicit scaled decomposition witnesses and inverse scaling, so angular distance invariance holds also when a decomposition family is empty. The quotient identity uses a strictly positive finite ENNReal multiplier; it remains valid for infinity and for equal points without applying an invalid infinity cancellation.

The slope proof sends each positive ball radius epsilon to t*epsilon, sends every nearby admissible tensor B to t-inverse*B, and checks locus membership, distinctness, and distance explicitly. Applying the inequality again with inverse scalar gives the equality. All ENNReal cancellation explicitly uses the positive multiplier's nonzeroness and finite value. I found no hidden continuity, finite-slope, or measure premise and no circular reliance on a conclusion of TR-06.

## Independent verification

I copied and compiled the inspected bytes in a separate scratch module root against immutable frozen Definitions, pinned Lean 4.33.1, pinned Mathlib, and LeanCert verification. Exit code 0, no warnings or errors. The six printed exports have only `propext`, `Classical.choice`, and `Quot.sound`; six `#assert_trust kernel` assertions passed. Their transitive closures cover the scaling/quotient/intermediate slope helpers. No Challenge import, `sorry`, `admit`, added axioms, `native_decide`, or computation oracle is used.

Actual command, source/snapshot identity, environment paths, timestamp and output are retained in `evidence/receipt.json` and `evidence/Homogeneity.log`.

This review proves no polar-volume formula, finite angular link integral, full-measure smooth locus, or complete TR-06 target. It is not an authoritative Linux Comparator run and does not justify a verified status or publication by itself. The George Stepaniants/Caltech authorship header and original Matthew J. Colbrook attribution are preserved without contact email.
