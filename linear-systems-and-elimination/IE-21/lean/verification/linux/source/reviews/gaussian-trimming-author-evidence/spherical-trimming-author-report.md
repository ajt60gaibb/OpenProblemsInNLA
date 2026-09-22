# Spherical trimming author milestone

Author: AI agent `reference_review`; this is author evidence, not an independent final referee report.

Source `NLA/IE21/SphericalTrimming.lean` SHA256 `b32b30a9d219524df83319537388966f3632a03c2304ebcd34f6438780dda0de`.

The exact frozen `spherical_gaussian_trimming` declaration is proved without added assumptions. The coupling is the actual normalized Gaussian direction law. Radius-direction independence factors its mean absolute error into the radial deviation times the spherical mean, which equals one. The exact centered squared-radius moment equals `2*n`; Cauchy–Schwarz yields the source constant `sqrt(2/n)`. The canonical Gaussian integral is connected through the already proved population-trimming identity. Zero Gaussian vectors cause no pointwise division issue: `norm_smul_gaussianDirection` holds also at zero.

The fresh macOS author build rebuilt all local prerequisites against cached pinned dependencies and compiled all four public declarations with axiom closures exactly `propext`, `Classical.choice`, `Quot.sound`. Receipt: `spherical-trimming-author-evidence.json`; commands, hashes and output: `spherical-trimming-typecheck.log`. No Comparator, LeanCert execution, dependency-from-source build, full IE-21 completion or status promotion is claimed by this receipt. The frozen boundary files were not changed.
