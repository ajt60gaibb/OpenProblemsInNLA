# IE-10 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of all specification/implementation authors. Phase: `lean-boundary`. Verdict: **APPROVE**.

KrylovCompression uses the full2n-coordinate independent real Gaussian product, builds the correct complex vector and normalizes its Euclidean norm, with a defined zero-draw fallback. CyclicShift has the original column-to-next-row orientation. Inner conjugates the first argument. The recursive GramSchmidt list contains exactly earlier normalized residuals; Column uses precisely the next residual and Basis has no out-of-range lookup. FullRank tests every j<k and failed residuals force an infinite compression condition number.

The compression is the actual conjugate-transpose Q* C Q. The spectral norm is the continuous-linear-map operator norm of the actual complex Euclidean matrix map. EigenvectorCondition takes the ENNReal infimum over all invertible exact complex diagonalizations. Its empty set has infimum top; repeated spectra and arbitrary column scalings remain included, and no attainment is required. Hence neither defective compression nor a rank failure can pass the finite ofReal threshold.

Target chooses positive real C,c once before every n>=3 and2<=k<n, uses real power n^c, and retains the original closed99/100 probability bound. Shared helper bodies preserve the approved mathematical semantics; both live and frozen targets now import the same recursive definitions, fixing identity mechanically without weakening the proposition. All actual helpers and pins are in the review closure.

The full canonical README equals ORIGINAL.md byte for byte; live/frozen namespace correspondence and complete local imports/pins are bound below. Author-local compilation and identity evidence was inspected against the current source hashes, with zero exits and only standard axioms. This review did not rerun Lean and claims no target proof, newly formalized correspondence lemma, external human review or Linux Comparator result.

## Reviewed input hashes

- `docs/lean/statements/IE-10/IMPLEMENTATION_NOTES.md`: `7e5260e85e8a9a10371eb3ca7683a8ddd9850d633533926b144867c5e6561785`
- `docs/lean/statements/IE-10/NUMERICAL_TARGETS.md`: `eec19ed42d3b851c634f3d775533002b4f9499a0e00f1ccd2a6d312e40529e7d`
- `docs/lean/statements/IE-10/ORIGINAL.md`: `61c9f5e820b4201e6b34e55cd43e3b65bc0e746dcdef6551ccfe50602ebe644a`
- `docs/lean/statements/IE-10/source-lock.json`: `e59ebef497522e57498b6cd6612e9f418fd3a51565cdb4a9af0dcc70b00305c9`
- `eigenvalues-and-inverse-problems/IE-10/README.md`: `61c9f5e820b4201e6b34e55cd43e3b65bc0e746dcdef6551ccfe50602ebe644a`
- `lean-statements/NLA/Statements/IE10.lean`: `55dd33eed940f0979222ae3f019a11192a9ee16e6d3b5c2ca5016c17b0079c74`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/KrylovCompression.lean`: `3d33cd4d2fff054a977cb3ff4ad796e4790b0ebcd83b4c46512ad42afc5cd7ce`
- `lean-statements/Reviewed/IE10.lean`: `b6535bc916f33aa3c37f7fcbef26791b1a0f79d767d2ce199cf7eb5feb3620ef`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
