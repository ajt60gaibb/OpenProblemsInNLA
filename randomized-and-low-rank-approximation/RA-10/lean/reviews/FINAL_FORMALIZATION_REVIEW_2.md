# RA-10 final formalization review 2

**Phase:** independent final source formalization review under `docs/lean/REVIEW.md`<br>
**Reviewer:** Codex AI agent `/root/ra10_second_referee` (independent referee; not the implementer or a human endorser)<br>
**Verdict:** **Approve the reviewed source bytes for fidelity and proof structure.** This is an AI source-review verdict, not a fresh Lean build, Comparator result, or human peer review.

## Reviewed identities

- Clean main source: `47006df8b3a6c724a557266c891893d03e69323a` in `solved-lean-statements/OpenProblemsInNLA`.
- PR #359 isolated wrapper source: `5c7d6fe9bfd6b85e53019ddff86a50d03af7bff4` in `ra10-isolated-verification/OpenProblemsInNLA`. I reviewed the single change from `b54a06955c88b82682ea7abe24a03b859af47435`: Mathlib's `configFile` entry in the wrapper `lake-manifest.json` changed from `lakefile.toml` to `lakefile.lean`. No theorem source, source lock, dependency revision, or target changed.
- Pinned substantive proof dependency: `844237f7e979146c937c0dc88f5c3f6e5f40c9b9`, `lean-statements` subdirectory. The final `OperatorMonotoneRepresentation.lean` import graph reaches **95 RA-10 proof modules**. There are 99 RA-10 proof modules in the pin; the four outside this import closure do not support this verdict.
- The 104-entry source manifest `docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/source-sha256.txt` has SHA-256 `4b3eb7816387b261c073b8b765f05d72badc0b9f191a3d502bf9bae689497e01`. I independently compared every listed SHA-256 with the corresponding file fetched from pinned commit `844237f7`; all 104 matched.

| Reviewed file | SHA-256 |
| --- | --- |
| Canonical `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| Complete prose solution `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/Reviewed/RA10.lean` | `9762f20d48ca7fbdfaf4b3a99809dddeccb20ad0ef9efe2b987a71de39495400` |
| `lean-statements/NLA/Proofs/RA10/OperatorMonotoneRepresentation.lean` | `6693ce2c817f554e6456eea6d7e2222d359f2f384b012a3e1881ccb682747521` |
| Wrapper `Challenge.lean` | `e6e5a0b18e6427f12cdf267291b82f7df4f255aac96bc8cdac7f034a52c33af2` |
| Wrapper `Identity.lean` | `e439017f98431648833a497da9c8340bde8cb4b86d9170a338cdeb0e38472617` |
| Wrapper `Solution.lean` | `c596533c2d1a83d1facfc398c6afa9d2b78423ef112bd9030ad60117beb7ee70` |
| Wrapper `source-lock.json` | `e598473d9f4445c5f130d989a4a1b627d9aed55638b0856238151b2aaad87602` |
| Wrapper `lake-manifest.json` at `5c7d6fe9` | `d03ac591181fc3122badad6a5c47a45ed1f5e994eea9e9fc990cb30ed85a5145` |

The PR changes none of the canonical README, complete solution, numerical specification, live statement, or reviewed statement from clean main. `source-lock.json`, `lakefile.toml`, and `lake-manifest.json` agree on the substantive proof revision. Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert at `621a43d7cf21f87872392a01e874f2f1dbddc926`.

## Fidelity and scope

The canonical target asks for one universal `C ≥ 1` before every input. `NLA.Statements.RA10.Target` has precisely that existential order; `ra10_target` constructs `⟨11, 1 ≤ 11, transferBound_eleven⟩`. `TransferBound` quantifies all `n ≥ 2`, `1 ≤ k < n`, all real matrices supplied with ordered PSD eigendecompositions, independent eigenbases for `A` and `Ahat`, all `ε ≥ 0`, and all functions continuous and nonnegative on `[0,∞)` and operator monotone for **every** positive matrix size. Its premise and conclusion use the same supplied basis for the two truncations of each matrix. The matrix pair has no order, commutation, invertibility, gap, positive-tail, or distinct-eigenvalue assumption.

The custom `NuclearNorm` is the sum of all `n` singular values of `Matrix.toEuclideanLin`, not an entrywise, Frobenius, operator, or signed trace norm. `PositiveSemidefinite` is real symmetry plus a quadratic-form inequality. `FunctionMatrix` is the full spectral sum; `FunctionTruncation` sums exactly the selected first `k` columns, even if their eigenvalues are zero. These definitions preserve arbitrary ties and `f(0)>0`. The reviewed and live statement files differ only in namespace; wrapper `Identity.lean` proves their `Target` equality by `rfl`. `Challenge.lean` contains a deliberate `sorry`; `Solution.lean` imports `Identity` and the pinned proof, not `Challenge`, and proves that exact reviewed target by rewriting the identity. `comparator.json` selects the single `NLA.RA10.target` theorem.

## Proof-path checks

I traced the final result through `transferBound_eleven_of_compactLoewnerRepresentation`, `compactLoewnerTransfer_eleven`, `loewnerAtomTransfer_eleven`, `ridgeTransfer_eleven`, `ridgeTransfer_of_compressionEstimate`, and `ridgeCompression_positivePart_trace_le`, then examined the supporting compression energy/mass/quadratic and positive-part trace arguments. The compression lemma is discharged for the **actual selected projection**; its assumptions include only a symmetric idempotent projection, PSD decompositions, and positive `s,c`. Singular compressions are handled using inverses of `sI+A` and `sI+PAP` with `s>0`, without an inverse of `PAP`. The scalar argument gives the exact factor `2/(s+c)`.

The matched-leading stage encodes source equations (8)–(14), including pinching, the positive-part trace identity, compression eigenvalue loss, the ridge scalar loss, and the restricted nuclear ideal bound. `SelectedApproximantPerturbation` proves the coefficient-one ordered-spectrum perturbation bound for the actual nuclear norm and keeps the supplied eigenvectors. The final arithmetic combines factor 5 with `r ≤ e` to obtain 11, and `RidgeScalar` proves the tail lower bound `τ_s ≥ τ/(s+c)` using exact real inequalities. There are no decimal certificates, sampling premises, or interval-coverage claims to inspect.

`ridgeTransfer_of_compressionEstimate` explicitly splits on zero input tail. In that case the approximation premise forces the selected truncated matrix to equal `A`, and the ridge error vanishes. In the positive-tail case it derives a positive cutoff rather than assuming one. The compact parameter has a constant atom at `t=0`, a linear atom at `t=1`, and positive scaled ridge atoms in between. The integration proof applies an atomwise bound to the full spectral error and identifies the exact selected optimal tail; it does not shrink a rank-deficient selected projection. The representation proof normalizes at `f(1)` (with a separate identically zero case), constructs the representing measure via the compact convex class, extreme-point classification, and a proved Hansen split, then extends it to zero by continuity and dominated convergence. The representation existence premise in the intermediate transfer theorem is discharged in the final theorem; it is not an added target hypothesis.

I scanned the 95-module final import closure and the statement files for `axiom`, `constant`, `opaque`, `sorry`, `admit`, `unsafe`, and `native_decide` declarations. No proof-path placeholder or custom axiom was found. The only `sorry` found in the isolated project is the intentional Challenge placeholder outside Solution's imports. I also inspected the stored `docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/build.log`: its printed transitive axioms for `ra10_target` are exactly `propext`, `Classical.choice`, and `Quot.sound`. This log is historical evidence, not an independently rerun build.

## Attribution, limits, and remaining gates

The canonical mathematical resolution remains credited to George Stepaniants, and both the canonical source and `formalization.yaml` disclose substantial Codex assistance. The wrapper identifies the substantive pinned source and does not claim that the Challenge placeholder proves the theorem. This review makes no historical-priority or human-endorsement claim.

I performed source inspection, import-graph and source-hash checks; I did **not** run a fresh Lean build, transitive axiom audit, or sandboxed Comparator in this worktree. There is no local `.lake` installation or `lake`/`lean` executable in this worktree environment. Those separate mechanical gates and any subsequent source-byte changes require their own verification. Approval is limited to the hashes above and the pinned 95-module dependency path; it does not cover the four unrelated RA-10 modules, external Mathlib/LeanCert implementation internals, or future revisions.
