# IE-21 matrix and finite-trimming author report

Status: implementation complete for the six assigned frozen semantic statements; awaiting independent review. This is author evidence, not an independent approval or a full IE-21 verification. No Comparator or complete LeanCert run is claimed.

## Stable modules and exact target statements

* `NLA/IE21/MatrixSemantics.lean` proves `matrix_semantics`, `deletion_minimum`, and `deletion_zero_cases`.
* `NLA/IE21/FiniteTrimming.lean` imports MatrixSemantics and proves `finite_trimming_semantics`, `directional_minimum`, and `statistics_measurable`.

`SignatureCheck.lean` restates each of these six signatures copied from the frozen Challenge and discharges it with the implementation theorem. It imports only the implementation, never Challenge. Full independent Comparator checking remains required later.

## Mathematical construction

The Euclidean operator norm is attained by compactness of the nonempty unit sphere; the usual continuous-linear-map bound identifies its maximum with the actual operator norm. Retained matrices are actual row submatrices, and their squared image norms are proved equal to the selected coordinate sum of squares.

The row count satisfies `floor(θm)≤m`. The domain of admissible row subsets times the unit sphere is nonempty and compact. Its image under the actual retained image norm is therefore compact; the real infimum belongs to that image and is bounded below by zero. This establishes the genuine minimum and every comparison inequality. Empty retained sets give zero directly; a nonzero retained kernel vector is normalized to give zero without any rank or conditioning premise.

For finite trimming, the family of exact-cardinality row sets is finite and nonempty. A minimizing selection has each selected value at most each omitted value: replacing one selected index by a smaller omitted value would decrease the sum. A nonempty minimizing selection therefore admits the maximum selected value as a threshold; the empty selection uses threshold zero. At that threshold the positive-part sum equals `k*t - selectedSum`. For every other threshold, the positive-part sum dominates the selected linear terms, proving the scalar maximum identity. Ties, `k=0`, `k=m`, and arbitrary nonnegative input values are covered.

The directional minimum follows by squaring the nonnegative attained norms and applying the finite selection minimum. Continuity of the deletion statistic follows from the compact-domain infimum theorem; finite trimming is continuous by the finite-domain version. The ratio is measurable even at zero denominators. Finally the all-directions GoodEvent is a closed intersection over every unit vector, combined with the closed covariance-norm constraint; no finite or countable net replaces its universal quantifier.

## Validation and limits

The fresh author build compiles Definitions, both proof modules, the six-signature check and the complete public-axiom audit with zero errors and zero warnings. All 21 exported theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`. Private compact-domain helpers are included transitively in these closures. No implementation imports Challenge or uses sorry, admit, custom axioms, native_decide, or computation outside the kernel.

All four frozen boundary/configuration hashes were checked unchanged against `reviews/statement-freeze.json`. No canonical page, status, Solution, shared metadata, or other agent's module was edited. Exact source and evidence hashes are in `author-evidence.json`.

Original source proof attribution remains Matthew J. Colbrook. Formalization credit remains George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, with no contact email added.
