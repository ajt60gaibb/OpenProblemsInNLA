# Independent review of the outside-row pivot candidate

Root read all 340 lines of GaussianPivotMasking.lean by
/root/source_statement_author, SHA-256
`61011b17993ab67650fe21d93cc4093bb59e303909f7421c000b666e48e5cffa`.

The exact original-label mask commutes with each Schur step if its selected
pivot label is outside the mask. A nonzero surviving maximal pivot keeps
the literal least-current-index rule: masked zeros cannot tie its positive
magnitude, while all surviving entries remain unchanged. Induction therefore
proves exact trajectory masking and pivot-prefix agreement, without a
no-tie assumption or nonsingularity of the masked matrix.

The deterministic fallback is a genuine outside-row injection under the
explicit cardinality bound. The candidate always avoids the removed rows,
is measurable, and factors through only the first m columns of outside
rows. On the actual nonzero avoiding prefix, its fallback is not selected
and its original labels agree exactly. This is sufficient for the later
fixed-candidate conditioning argument; it does not condition Gaussian rows
on becoming the next selected rows.

Approved exact statements and proof. Root independently compiled the exact source: all 29 kernel checks passed,
with foundational axioms only and no warnings; final selected-block extension remains to be proved.
