RE05 actual spectral charge and source query count
=================================================

The three new modules prove symmetry and positive semidefiniteness of the
unchanged literal leverage matrix, a trace identity for every literal valid
square SVD of a PSD matrix, the actual selected-column spectral charge, and
the complete deterministic `NLA.Statements.RE05.SourceQueryBound`. They do
not prove the Gaussian success probability, `OriginalClaim`,
`SourceCompanion`, or the full RE05 `Target`. No Linux, Comparator, canonical
package, or status-promotion claim is made.

`LeveragePSD.lean` identifies the actual leverage entry formula with
`∑ j, E_j * E_j.transpose`, where every `E_j` is the actual model's
`orthonormalMember P j`. It derives symmetry and PSD without requiring
independence, a chosen basis, or nonzero normalization branches.

`PositiveSVDTrace.lean` takes the exact `SVDMachine.ValidSVD` relation. The
square-index reindex is precisely `Fin.cast (Nat.min_self n).symm`, as in the
actual query model. Finite reconstruction and the two actual full column
orthogonality clauses give `B*v_j = sigma_j*u_j` and
`B.transpose*u_j = sigma_j*v_j`. PSD implies symmetry. Applying its quadratic
form to `u_j-v_j` gives

    0 <= -sigma_j * sum_i (u_ij-v_ij)^2.

The two unit column norms express that sum as `2-2*dot(u_j,v_j)`.
Together with nonnegative singular values, this forces the weighted identity
`sigma_j * dot(u_j,v_j) = sigma_j`. It also covers `sigma_j=0`; no equality
of the left and right zero-singular bases is asserted or assumed. Reordering
the finite reconstruction sums therefore gives `trace B = sum_j sigma_j`
for every actual legal SVD tuple, including ties and empty dimensions.

`SelectedCharge.lean` applies that theorem to the actual `exactSVD (leverage P)`
using the previously proved literal `svd_total`, not an SVD availability
premise or a different spectral decomposition. The accepted actual fold
theorem gives the trace `q+1`. A separate finite-filter inequality proves that
the actual selected-list length times its threshold is at most the sum of
all nonnegative singular values. This inequality needs no positivity of the
threshold, so `selectedCount_charge` holds for every real accuracy parameter
under only the unchanged `Independent P` hypothesis. The final positive
accuracy hypothesis is used by the frozen analytic width/count bridge in
`QueryCount.lean`; its spectral-charge obligation is completely discharged.
The resulting `sourceQueryBound` is the literal deterministic uniform bound
for every random stream and the actual fifteen-copy committed batch.

No original, ID, model, Target, canonical page, status, or catalog was edited.
All 18 original/model/review/registry/pin inputs and all frozen prerequisite
sources are checked before and after replay. The previously accepted custom
fold proofs, root attained/SVD/orthogonal-optimum sources, and the exact
frozen `QueryCount.lean` are unchanged.

All three producer modules and the final development consumer passed
LeanCert kernel mode with only the standard three axioms or a subset. The
first consumer preflight had Matrix namespace lookup and finite identity
equality-orientation errors; its exact input and raw log are retained.
Those corrections changed only the consumer. The passing development
consumer reused prior private development objects and is not fresh evidence.

The separate fresh replay snapshots all local producers and begins with an
empty private project output root. Its 25 explicit positive assertions cover
all 14 new declarations, expanded literal leverage/selected-list/source-bound
statements, every legal PSD SVD, the actual chosen zero-matrix SVD, and the
legal zero-SVD tuple with opposite full bases `U=I`, `V=-I`. A negative
threshold control checks that positivity was not silently added to the finite
filter theorem. The reviewed full-target identity is an identity check only.
A separate unresolved-False control must fail kernel trust with `sorryAx`.
`final/result.json` is authoritative for the terminal fresh result. This
document is author analysis, not an independent source-review approval.
