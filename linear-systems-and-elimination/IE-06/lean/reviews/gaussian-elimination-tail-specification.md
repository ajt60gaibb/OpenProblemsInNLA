# Exact Gaussian elimination-tail transfer

Author `/root`; independent approval by `/root/source_statement_author` before
implementation. For L≥0 and x>0, under the literal Gaussian matrix law, bound

P{every row of every canonical E_k, k<n, has squared Euclidean norm≤L,
   and rawSchurMax>sqrt(2xL)} ≤ 2 n³ exp(-x).

The transfer is unconditional as a probability inequality. Each stage k and
column j≥k uses the exact product joint law of E_k and original column j.
The fiber event is empty when that stage's row-norm guard fails, and otherwise
GaussianLinear.rows_tail bounds it by 2n exp(-x). Integrate this bound, then
union over at most n² stage-column pairs. The all-stage good event is used only
for containment; it is never made a conditioning hypothesis in a Gaussian law.
The exact left-operator identity relates the resulting linear forms to Schur
entries. No admissibility/nonsingularity hypothesis is needed for this algebra.
Dimension zero and L=0 are included using strict events and nonnegative norms.

The resulting original normalized exceedance bound is at most the probability
that some canonical row squared norm exceeds L, plus 2n³ exp(-x), plus the
proved exact normalization exception q^(n²). This remains a transfer lemma;
the required strong bound on canonical row norms is a separate theorem.
