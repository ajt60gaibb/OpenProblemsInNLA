# Independent review: path existence and Gaussian nonsingularity

Date: 2026-10-06. Reviewer: mathematical-review agent, independent of the
implementers of the three modules below. This review concerns source-level
proof correctness; retained compilation and transitive-axiom receipts are
separate execution evidence.

| Reviewed module | SHA-256 |
| --- | --- |
| `NLA/IE06/Pivot.lean` | `be17ad9e8ca2ddad1559968fe0ad91abf0b9ce127c17c5bdf665a14976455739` |
| `NLA/IE06/GEPP.lean` | `28c6de0c446c07d151d59bf8c3b8576255eac6163400ef8ba77dac0e2f6efd36` |
| `NLA/IE06/GaussianNull.lean` | `891317066c2be9dd615651ad0beb29a96c2b8749413f9fac7f336e4bca2b0ef8` |

## Deterministic path construction

The auxiliary scan in `Pivot.lean` iterates current row indices in ascending
order, retaining the earlier candidate on equal magnitude. It begins with
the current pivot row. The score `-1` assigned to inactive rows is strictly
below every active absolute value, so inactive rows cannot win. The proof
relating the scan to `List.argmax` handles maximality and least-index ties
without assuming that the column contains a nonzero entry.

The separate nonzero-column lemma upgrades this maximizer to an admissible
pivot. This separation is mathematically necessary: an all-zero column still
has a maximum but no permitted nonzero pivot. `firstTrajectory`, `firstPath`,
and their equality lemma retain the exact previously reviewed row-swap/Schur
recursion. Uniqueness in this module concerns the specified first-available
tie rule only; it does not claim arbitrary admissible paths are unique.

`GEPP.lean` proves the intended unconditional path-existence obligation from
`A.det ≠ 0`. Its active-injectivity invariant acts on vectors supported in
the active columns and tests only active rows. It correctly avoids asserting
nonsingularity of the zero-padded full matrix.

Initial nonsingularity gives injectivity of matrix multiplication. A zero
active pivot column would annihilate a supported coordinate vector, so some
active entry is nonzero. Swapping two active rows preserves injectivity.
The Schur step preserves the invariant by extending a vector in the Schur
kernel with a pivot-coordinate value that cancels the pivot row; the chosen
pivot is explicitly nonzero. The resulting vector lies in the earlier
active kernel, forcing the original vector to vanish. The displayed
matrix-vector identity uses the same row swap and Schur expression as the
canonical definitions.

Induction therefore constructs a valid first-available path at every stage
through dimension `n`. The final existence theorem supplies that witness to
the unchanged `AdmissiblePath` predicate. Dimension zero is handled by its
vacuous path and does not require an invented pivot. No property of the
Gaussian law or growth factor is assumed in this argument.

## Gaussian null-polynomial argument

`polynomial_ne_zero_ae` has the correct general hypothesis: a nonzero real
polynomial evaluated on a finite product of atomless probability laws.
The zero-variable case is a nonzero constant. In the successor case, a
nonzero coefficient polynomial is nonzero almost everywhere by induction.
For those coefficient values the remaining univariate polynomial is nonzero,
has finitely many roots, and its root set has zero mass under the remaining
atomless marginal. The proof establishes the needed joint measurability
before its product almost-everywhere and Fubini steps. It transports the result
back through the explicit finite-product measurable equivalence.

The nested rectangular Gaussian law is flattened by actual measure-map
identities for uncurry and the finite product-index equivalence. It is not
replaced by an unspecified independent random-variable model.
`minorPolynomial` is a determinant polynomial in those concrete entry
coordinates. Evaluation commutes with the determinant, and evaluation at an
embedded identity matrix proves that polynomial is nonzero. Thus the leading
square minor is nonzero almost everywhere. The proof also covers the empty
minor, whose determinant is one.

Finally, square dimensions and the identity `Fin.castLE` turn this result
into exactly

```lean
gaussianMatrix n {A : Mat n | A.det = 0} = 0
```

No conditioning on nonsingularity, source theorem, or additional stochastic
axiom appears. The adaptation cites its local source and imports no external
project proof module. Kernel-trust assertions cover the exported probability
argument and final obligation.

## Disposition

**Approved at the hashes above.** No hidden assumption, weakened conclusion,
or mathematical defect was found. These modules complete the exact
admissible-path existence and singular-nullity obligations. They do not prove
Gaussian absence of pivot-magnitude ties or the square-root growth tail;
those remain logically separate targets.

Follow-up: the final Gaussian wrapper uses an explicit function-eta equality
to identify the square rectangular minor with the actual matrix determinant.
I reviewed that elaboration repair and independently recompiled all three
modules as dependencies of GaussianTies using the pinned local runtime/cache.
All compile and their exported kernel-trust checks succeed, with only the
permitted foundational axioms. The updated GaussianNull hash is recorded above.
