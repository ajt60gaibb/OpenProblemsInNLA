# RA-19 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of specification/implementation authors. Phase: `lean-boundary`. Verdict: **APPROVE**.

Square d covers exactly n=d+3>=3. The inspected Matrix.adjugate API is the transpose of the cofactor matrix; trace(adj(X)*Z) is the full determinant differential even when X is singular. SmoothPoint includes both variety equations and a nonzero restricted differential. The reduced-hypersurface Jacobian correspondence reviewed in the specification makes this exactly the smooth locus, including exclusion of gradient-degenerate rank-n-1 points.

Critical retains all tangent directions with Z00=0 and determinant differential zero, and the full same-index bilinear displacement sum. There is no conjugation, inverse formula, rank-only surrogate or selected Lagrange solution. The omitted common derivative factor2 is nonzero over Complex.

The actual MvPolynomial is in every data entry, has an explicit nonvanishing witness, and precedes all data in its principal open. The full Critical subtype is equivalent to Fin(5*(d+3)-7), so finiteness and the exact number of distinct smooth critical points are both required; no infinite-cardinality default or sampled subset can satisfy it.

The full canonical README equals ORIGINAL.md byte for byte. Frozen source matches the live namespace transformation; all local imports and pins are bound below. This report is a static independent source/mathematical review; it makes no new compilation claim. No Target proof, fresh Linux Comparator run or external human review is claimed.

## Reviewed input hashes

- `docs/lean/statements/RA-19/IMPLEMENTATION_NOTES.md`: `971186a309c62ab5b835ca6c5a32e0122620f8a3d837b155412a04a26ef320d5`
- `docs/lean/statements/RA-19/NUMERICAL_TARGETS.md`: `2576b6a692a79ee6ce96c11910363d9b1ec951f7363547f9af8d5d1108d95c6e`
- `docs/lean/statements/RA-19/ORIGINAL.md`: `e952b7183d746bae9c3750ac47e8e2a878808e5287a56bf3b106f44c975c8db3`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/RA19.lean`: `680a77490e093611c835ab6d074e67267274474d22c12158490da5aaade63845`
- `lean-statements/Reviewed/RA19.lean`: `1113d22daab22f1e4eeee3f4d7b9bd0b4dc8eadf4268abafdb83b1dd563e8384`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `randomized-and-low-rank-approximation/RA-19/README.md`: `e952b7183d746bae9c3750ac47e8e2a878808e5287a56bf3b106f44c975c8db3`
