# RE-06 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the RE-06 specification, live Lean module, frozen module, or shared query machinery. This is a review of the exact target boundary, not a proof of its success theorem.

I compared the canonical README, approved numerical specification, source algorithm in `solution.tex` (especially parameter rules and §§2,5–6), and both Lean boundaries. `Family n m` enumerates exactly `m+2≥2` distinct matrices; injectivity enforces the finite set cardinal. `OriginalClaim` places one positive constant, a nonnegative integer logarithmic exponent, and one fully specified uniform algorithm before every dimension, family, arbitrary target matrix, and `0<ε<1/2`. `ExplicitClaim` retains the source coefficient 4,000,000 and exponent zero. Both use a worst-case count and the exact `99/100` success threshold.

The shared operational code constructs an entire ordered right/left query list from explicit inputs and Gaussian draws before reading any oracle answer. The only use of the unknown matrix in `run` is through `oracleAnswers`, which maps the fixed list through the actual `Av`/`Aᵀv` oracle. `postprocess` receives only stored responses, explicit candidates, and the committed plan. The widths implement `ceil(log₂(2M))`, `ceil(sqrt L)`, and the exact source formulas for `s,k,ℓ`; the branch `n≤s+k+ℓ` queries all standard basis vectors and recovers `A`. The nontrivial branch uses disjoint standard-Gaussian coordinate blocks, the source-authorized unscaled first sketch, finite tie-broken candidate scans, residual sketches from stored answers, and an SVD-based pseudoinverse defined on rank-zero and deficient inputs.

`optimum` is the attained finite Frobenius minimum, and `Successful` tests the returned member against `(3+ε)OPT` for every fixed input. The exact-real SVD primitive has an explicit validity predicate, and `SVDTotal` is asserted as part of `Target`, not an unproven premise. This is a concrete model with only oracle calls charged; the output uses no hidden access to `A`. The infinite Gaussian product law is sampled through finitely many stream coordinates per execution, so it supplies the finite independent blocks.

The agent independently checked pinned build, LeanCert kernel trust and a fresh live=frozen `rfl` identity. I checked the source-level semantics and hash-bound import closure below. This does not assert the mathematical theorem was proved or the Linux Comparator run executed.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/RE-06/NUMERICAL_TARGETS.md` | `ed37af5809b15afd1f9b4411356eaba15fceb9d988f41b0c7a5cda9089044865` |
| `docs/lean/statements/RE-06/ORIGINAL.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `lean-statements/NLA/Computation/NonadaptiveMatrixQuery.lean` | `66345a3ed3274e6dd351ffaa7e1b75a0aa95afa63c3ece937d37f1efaad29b21` |
| `lean-statements/NLA/Computation/SVDMachine.lean` | `8ec5866326b5a311b334651600db5d7f3065f2059175823626319afef7cf7581` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/RE06.lean` | `847ac668ce6a7c99569bab0d1a0ca5a5bc1a471a9938a2a31d19208b9ca5aa00` |
| `lean-statements/Reviewed/RE06.lean` | `6e8b552f4f1d8b3bd330a1748b915b0ebdd5e5f15427ce59a2d7b531493d45f1` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `randomized-and-low-rank-approximation/RE-06/README.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
