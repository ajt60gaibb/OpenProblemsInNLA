# FR-10 independent Lean boundary review

Reviewer: `/root/fr05_review`, independent of the FR-10 Lean implementation.
Phase: `lean-boundary`. Verdict: **APPROVE** the statement boundary. This is
not a proof of the Walsh sampling theorem or a Linux Comparator certificate.

## Reviewed input hashes

These are every local input in the union of `review_inputs(...,
"lean-boundary")` for the live and frozen FR-10 modules, as computed by
`tools/lean_statements/check.py`:

| Input | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-10/README.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/ORIGINAL.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/NUMERICAL_TARGETS.md` | `4302bb580024b66b0bdc7e65e493eefdba2ae33659c7181757f5965aea85cad3` |
| `lean-statements/NLA/Statements/FR10.lean` | `001753ea5a5560ab962558f5030e20108bb1d4b322c3d98f46397787afe09b92` |
| `lean-statements/Reviewed/FR10.lean` | `78aa805bc9cc5b4c386e1e0387d93a559991d85cc0bc4183fe56522f034fcbf3` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

The local import closure contains exactly the live FR-10 file, the frozen
FR-10 file, and `NLA.Statements.Infrastructure`. Their external imports are
bound by the package manifest: Lean `v4.33.1`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert commit
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The checked-out Mathlib
and LeanCert package HEADs match those two manifest commits. The frozen file
is exactly the output of the repository's freeze transform: one leading
comment plus replacement of `NLA.Statements.FR10` with
`NLA.ReviewedStatements.FR10`; an independent byte comparison returned true.

## Mathematical boundary

- `Index d = Fin d → ZMod 2` has `2^d` elements and models the source's
  `𝔽₂^d`. `walshSign` (live lines 20–23) raises `-1` to the sum of products
  of the canonical `0`/`1` representatives. Reduction of that exponent
  modulo two is exactly the field dot product, so the sign is
  `(-1)^(a·b)`; no phase or normalization is lost.
- `sampledEnergy` (lines 33–37) is the exact squared norm of
  `Φ = √(N/m) H_(a₁,…,aₘ),:` for positive `m`, after cancelling
  `√(N/m) N^(-1/2) = m^(-1/2)`. `RIP` (lines 39–44) requires one sample to
  satisfy both weak inequalities for **all** real vectors with at most
  `k` nonzero coordinates. The `Fin m → Index d` sample allows repetitions,
  ordered independent draws, and `m > N`.
- `successProbability` (lines 46–52) counts successful ordered samples
  among exactly `(2^d)^m` equally likely tuples. `Qualifies` uses the exact
  inclusive threshold `9/10` and `m ≥ 1` (lines 54–55). `mStar` is the
  infimum over these natural counts; `IsMinimumSampleCount` (lines 60–65)
  explicitly requires membership and leastness. `Target` asserts this for
  every admissible `d,k`, preventing the empty-set `sInf = 0` case.
- `Rate` (lines 67–71) uses natural `Real.log` and `e = exp 1`, with the
  source factors `k log(2k) log(2e·2^d/k)`. `Target` (lines 84–91) covers
  `d ≥ 1`, `1 ≤ k ≤ 2^d`, the `k=1` endpoint, and one universal positive
  pair `c,C` for **all** `2 ≤ k ≤ 2^d`, including `d=1,k=2` and `k=N`.
  `ManuscriptQuantitativeBound` (lines 73–79) separately records the
  manuscript's explicit `1/2000` lower coefficient with a universal upper
  constant. It does not silently replace the original existential target.

## Elaboration and limits

`PATH=/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin:$PATH lake build NLA.Statements.FR10 Reviewed.FR10`
completed successfully (`1953 jobs`). Both modules ran
`#assert_statement` and `#assert_trust kernel` on both named targets.
The printed axiom closure of each `Target` was exactly `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, new axiom, unsafe
declaration, or native decision command appears in the three local files.

No mathematical or numerical mismatch was found. A source-to-Lean equivalence
lemma for the square-root matrix expression is useful if the project later
publishes a full proof, but the displayed energy cancellation is exact and
does not block this statement-only boundary. This review does not establish
the truth of either target, run an isolated Linux Comparator check, or promote
FR-10 to `Lean verified`.
