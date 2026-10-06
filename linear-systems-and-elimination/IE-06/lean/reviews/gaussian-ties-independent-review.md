# Independent pivot-tie review

Reviewer `/root`, independently of implementation agent
`/root/independent_math_review`. Reviewed `NLA/IE06/GaussianTies.lean`, SHA-256
`36009718e4410ea33a4a6d5c3619932f37d6b01dac04ae028818b9a6e3bda5b5`.
The exact algebraic route received preimplementation review.

The common-denominator update is correct: if S=N/D and the pivot numerator
is P, then the updated numerator is N_ij P - N_ik N_kj, and the common
denominator is D P. Prefix pivot nonvanishing proves both evaluated factors
nonzero before any division cancellation.

Polynomial nonvanishing uses a backward realization of a supported tail whose
one tested entry is one and the other zero. The construction inserts pivot
one, zero pivot row/column, and undoes the prescribed swap. It requires active
prefix positions, as it must; it does not improperly claim nonvanishing for
arbitrary invalid paths. The tail itself may be singular, which is sufficient
for a polynomial witness. Equality of absolute entries implies equality of
squares and hence vanishing of this nonzero polynomial.

The Gaussian null theorem is applied to the actual vectorized product law.
The union is over finitely many paths and indices at each fixed n; this incurs
zero exceptional probability, not a factorial probability loss. Paths with
invalid prefixes are excluded by admissibility. Outside the resulting null
set every active column has distinct absolute entries. An induction on the
trajectory proves that any two admissible paths agree. Gaussian nonsingularity
and GEPP existence give actual existence, then agreement with firstPath.
Dimension zero is included by the empty path type.

The exact all-admissible-path semantics are retained. This discharges the
null-tie bridge to the source's deterministic pivot rule without changing the
original event. Mathematical and statement review approved. Individual kernel
and axiom checks are recorded in the author's retained compile receipt; the
full probabilistic tail is still an independent outstanding theorem.
