# Notes

The main repair is to avoid freezing b during the projection reduction. The function K -> ||[S^(1/2) K S^(1/2),log S]||_1 - h(tr SK) is convex on the full positive-contraction interval. Its spectral convex decomposition is an elementary finite-dimensional proof; no generic extreme-point theorem is needed.

The zero and identity projections contribute zero to both sides. The limiting argument uses positive definite S throughout and therefore never takes log of a singular matrix.

The sharpness family is already 2-by-2 and is strictly positive after regularization. Its entries are rational whenever t is rational. The unregularized rank-one version alone would not meet the repository's strict positive-definiteness assumption.

Failed/general approaches: direct triangle inequalities in the resolvent integral for log lose the sharp coefficient; a restriction to rank-one P is not justified; a fixed-weighted-trace projection assertion is false. No dimension reduction from arbitrary projections to 2-by-2 blocks has been established.

Useful next target: prove the projection inequality with the exact weighted trace h(tr SP), rather than an entropy bound with an additional coefficient or a rank-dependent estimate.
