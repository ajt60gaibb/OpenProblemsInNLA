# Proof and status audit

## Established in the new report

1. A Gaussian block least-singular-value tail bound with explicit constant 16,
   proved using orthogonal invariance, a row-distance identity, and a scalar
   Gaussian small-ball estimate.
2. Deterministic barycentric scaling inequalities, including a tail-to-head
   normalization bound independent of the overall spectral condition number.
3. A graph-subspace theorem for narrow bands. Its explicit width assumption is
   part of the theorem, not a technicality that can be omitted.
4. A generic block-Vandermonde rank theorem, proved by a balanced-coloring witness.
5. Exact recovery after L + ceil(rho/b) Krylov blocks when L is the number of
   distinct eigenvalues strictly below the cutoff, with zero counted when present.
6. A concrete boundary-multiplicity example showing that replacing ceil(rho/b)
   by ceil(k/b) without qualification can fail for exact recovery.

## Imported dependencies

The implication from a quantitative good-start graph to all three RA-04 output
guarantees uses the Chen et al. good-start convergence result, as identified in
the previous report. This continuation does not present a new independent proof
of that convergence theorem.

The fixed-spectrum, all-failure-probability narrow-band corollary additionally
uses the previous report's all-input bound with the extra t log m term. That
bound is explicitly attributed and is not represented as freshly re-proved here.

## Unresolved

For arbitrary admissible spectra, t and b growing, and nonzero cluster widths
outside the new explicit restriction, the desired universal bound remains
unproved in this archive. The earlier general bound still has an extra t log m.

The sufficient square-depth interpolation estimate in the previous report is
not proved here. Additional Krylov powers could still bypass that estimate;
its failure, were it established, would not alone refute RA-04.

Neither exact finite checks nor numerical examples establish the missing
unrestricted estimate, a universal asymptotic constant, or novelty relative to
all existing literature. The status remains PARTIAL, not SOLVED.
