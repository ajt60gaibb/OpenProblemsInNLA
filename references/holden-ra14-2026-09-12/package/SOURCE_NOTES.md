# Primary sources and proof dependencies

Checked against the public websites on September 12, 2026. The bibliography in
`report.pdf` contains the same four primary sources. External complexity results
are imported, not reproved or formally verified by the accompanying code.

## [RA14] Problem specification

Open Problems in Numerical Linear Algebra, “RA-14 — Optimal query complexity of
spectral rank-k approximation.”

Repository location:
`https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RA-14`

Raw statement:
`https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-14/README.md`

Dependency: report Section 1. The target has success probability 99/100 for every
input, charges each individual product Ax or A^T x separately, and asks for all
simultaneous finite parameter regimes. The note uses precisely that oracle model.

## [MM15] Global Krylov upper bound

Cameron Musco and Christopher Musco, “Randomized Block Krylov Methods for
Stronger and Faster Approximate Singular Value Decomposition,” 2015.

`https://arxiv.org/html/1504.05477`
`https://arxiv.org/abs/1504.05477`

Locations: Algorithm 2 and Theorem 10, together with the spectral approximation
analysis. Dependency: report Theorem 1.1 and Section 3. The algorithm is applied
to A^T so that the output is a right approximation subspace. The report separately
accounts for each vector query and the final compression. The exact-column branch
handles the finite-dimensional cap. No numerical value for the theorem's universal
iteration constant is inferred from the experiments.

## [SAR18] Adaptive PCA lower bound and hard distribution

Max Simchowitz, Ahmed El Alaoui, and Benjamin Recht, “Tight Query Complexity
Lower Bounds for PCA via Finite Sample Deformed Wigner Law,” STOC 2018;
arXiv:1804.01221v2, June 27, 2020.

`https://arxiv.org/html/1804.01221`
`https://arxiv.org/abs/1804.01221`

Locations: Theorem 1, Proposition 2.1, and Theorem 2.2. Dependency: report
Section 6. Theorem 1 provides the asymptotic all-adaptive query lower bound.
Theorem 2.2 identifies the conditioned deformed-Wigner distribution;
Proposition 2.1 provides the stronger spectral event used in the reduction.
The report retains all polynomial dimension hypotheses and does not use the
source's explicit constants to claim a sharp threshold. The exact graph and
polynomial postprocessing argument connecting this theorem to RA-14 is proved
in report Section 5; it is not asserted to be a theorem in this source.

## [BN23] Rank-one spectral lower bound

Ainesh Bakshi and Shyam Narayanan, “Krylov Methods are (nearly) Optimal for
Low-Rank Approximation,” arXiv:2304.03191v1, 2023.

`https://arxiv.org/html/2304.03191v1`
`https://arxiv.org/abs/2304.03191`

Locations: Theorem 1.1, Theorem 5.2, Section 6, and Open Question 1.10.
Dependency: report equation (1.4) and Section 7. The bounded symmetric hard
family has second singular value 1 and norm below 2 for the stated accuracy
range. The report retains a sufficiently-large-dimension threshold of order
at least epsilon^(-2.01), allowing enlargement of universal constants.
The lossless rank-padding extraction is proved in the report. The source's
lifting method is not treated as a vector-query direct-sum theorem.

## Attribution boundary

The global Krylov theorem, the deformed-Wigner information bound, and the
rank-one spectral lower bound are external proof dependencies. The Gaussian
rank lower-bound argument, sharp overlap example, weighted graph/Fejer
postprocessor, and padding extraction are written out in this package.
Their inclusion is not a claim that they are unprecedented in the literature.
No exhaustive literature-priority search or independent peer review is claimed.
