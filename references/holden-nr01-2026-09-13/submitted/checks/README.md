# Verification records

`release/summary.json` summarizes successful staged verification. Each algebra
file has one record per canonical selected pattern, in the order of the
corresponding `data/patterns_n*.json` file. Indices are zero-based.

`linear_columns` is the number of bivector coordinates. `nullity_mod_prime` is
the dimension of the exact specialized linear kernel. `complementary_pairs`
lists its known decomposable spike directions. `quadratic_rank` is the exact
rank of the coefficient matrix obtained by restricting all Plucker quadratics
to that kernel. `quadratic_target` equals choose(nullity+1,2) minus the number
of complementary pairs. Equality meets the sufficient exclusion criterion in
Lemma 7.1 of the report; the planar-section lemma then rules out a bounded lift.

The second prime for each size uses a different coordinate gauge and a smaller
necessary determinant subsystem. It is an additional arithmetic cross-check,
not a logically necessary second proof input.

Successful run logs are supplied alongside this file. Release verification was
completed in individual stages. Each stage can be rerun independently using
the README commands, or through the full driver. The summary-only command
checks saved-output completeness and consistency; it does not rerun any rank
calculation. The thirteen regression tests supplement, rather than replace,
the six exhaustive algebra passes and the geometric completeness argument.
