# IE-21 proof status

The approved target is preserved in `Challenge.lean`: `theta ∈ (0,1)`, the
floor `⌊theta*m⌋`, the variational row-deletion quantity, spherical independent
rows, arbitrary sequences with `n → ∞` and `m/n → ∞`, both component limits,
and the ratio limit. The quantitative source claims (the `L`, `epsilon`,
`t`, `delta`, covariance and trimming failure bounds, moment/MGF estimates and
`O_theta` rate) are recorded verbatim in `SPEC.md` and remain proof obligations.

No complete proof is claimed. The current blocker is the missing formal
probability infrastructure for independent Haar-uniform surface laws on
varying-dimensional spheres and convergence in probability for a sequence of
different measurable spaces. `SphericalRowLaw` is therefore an explicit
semantic boundary record in this scaffold and is marked as a fidelity divergence in
`formalization.yaml`; it must be replaced by a definition using the
dimension-`n-1` Hausdorff/surface measure and product measures before a
kernel-checked theorem can be accepted. The current `Solution.lean` proves
only definitional support lemmas and does not import `Challenge.lean`.

The local machine has no configured elan toolchain, so no Lean, LeanCert or
Comparator command has been run. See `verification-commands.txt`.
