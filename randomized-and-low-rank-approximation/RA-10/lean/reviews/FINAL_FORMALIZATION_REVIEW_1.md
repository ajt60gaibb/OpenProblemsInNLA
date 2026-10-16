# RA-10 final formalization review 1

**Phase:** final proof and wrapper review, 2026-10-16.<br>
**Reviewer:** OpenAI Codex AI agent `/root/ra10_full_audit`, independent of the implementation work on PR #359.<br>
**Verdict:** **APPROVE the source-level target correspondence and proof structure for the exact bytes below.** This is one independent AI-agent review, not human peer review and not a claim that the isolated Linux Comparator gate has passed. Retain `Solved` until that gate and the remaining independent final review are complete.

## Reviewed revision and source lock

I read the RA-10-only wrapper at PR #359 head `5c7d6fe9bfd6b85e53019ddff86a50d03af7bff4`, based on published main `47006df8b3a6c724a557266c891893d03e69323a`. Its `lakefile.toml` and `lake-manifest.json` both pin the `lean-statements` subdirectory of this repository at `844237f7e979146c937c0dc88f5c3f6e5f40c9b9`, Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

| Input | SHA-256 |
| --- | --- |
| Canonical `RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| Live `NLA/Statements/RA10.lean` in pinned package | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| Frozen `Reviewed/RA10.lean` in pinned package | `9762f20d48ca7fbdfaf4b3a99809dddeccb20ad0ef9efe2b987a71de39495400` |
| Final `NLA/Proofs/RA10/OperatorMonotoneRepresentation.lean` | `6693ce2c817f554e6456eea6d7e2222d359f2f384b012a3e1881ccb682747521` |
| Complete 104-entry proof source manifest | `4b3eb7816387b261c073b8b765f05d72badc0b9f191a3d502bf9bae689497e01` |
| Wrapper `Challenge.lean` | `e6e5a0b18e6427f12cdf267291b82f7df4f255aac96bc8cdac7f034a52c33af2` |
| Wrapper `Identity.lean` | `e439017f98431648833a497da9c8340bde8cb4b86d9170a338cdeb0e38472617` |
| Wrapper `Solution.lean` | `c596533c2d1a83d1facfc398c6afa9d2b78423ef112bd9030ad60117beb7ee70` |
| Wrapper `comparator.json` | `dc975d9412cbc151a572f898ce585d46e9e7b8e5be895501fc352b33ae0ca6c5` |
| Wrapper `lakefile.toml` / `lake-manifest.json` | `b7864c04dcb29195760df36e6333f7089dc7c628ef9d04b1499bff33974e9f45` / `d03ac591181fc3122badad6a5c47a45ed1f5e994eea9e9fc990cb30ed85a5145` |

I independently compared every manifest entry with `git show 844237f7:lean-statements/<path>`: **104 entries, zero mismatches**. The final theorem's import closure contains 95 RA-10 proof modules, plus the live statement/infrastructure and pinned Mathlib, LeanCert, and Lean imports. It imports no proof from another problem. The later `RidgeCompressionEq6Eigenvector.lean` on main is outside this closure and outside the pinned revision.

## Statement fidelity and wrapper

The original asks for one real `C ≥ 1`, independent of every dimension, rank, PSD pair, eigenbasis choice, error parameter, and admissible function. The frozen `Target` keeps `n ≥ 2`, `1 ≤ k < n`, nonnegative `ε`, the actual sum-of-singular-values nuclear norm, and all-size real PSD operator monotonicity. It quantifies both ordered orthonormal decompositions and uses each selected basis in both ordinary and functional truncations. Thus ties, selected zero eigenvalues, `f(0) > 0`, zero optimal tail, and noncommuting matrices remain in scope. Its `AdmissibleFunction` imposes continuity and nonnegativity only on `[0,∞)`. The prior independent specification and Lean-boundary reviews are bound to the unchanged statement hashes above.

`Challenge.lean` imports only `Reviewed.RA10` and presents the complete frozen proposition as `NLA.RA10.target`; its single `sorry` is confined to the challenge. `Identity.lean` proves by `rfl` that live and reviewed `Target` propositions are equal. `Solution.lean` imports that identity and the pinned full proof, rewrites to the live target, and applies `NLA.Proofs.RA10.ra10_target`. The pinned theorem supplies `⟨11, by norm_num, transferBound_eleven⟩`, so the wrapper neither adds a hypothesis nor replaces the original existential target by a restricted case. `comparator.json` selects precisely `NLA.RA10.target`, has no replaceable definition holes, and permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Proof and numerical path inspected

I traced the source-level path through the final theorem and the main nontrivial bridges. `HansenSplit` proves the two canonical nonnegative operator-monotone divided-difference pieces, discharging the analytic split premise. `OperatorMonotoneCompactness` applies Krein–Milman to the closure of normalized genuinely admissible positive profiles; `LoewnerMeasureConstruction` obtains a measure from the closed convex hull of harmonic atoms. `CompactLoewnerEndpoint` extends the representation to zero by dominated convergence. No representing-measure existence is assumed by the exported theorem.

`LoewnerAtomTransfer` handles the constant endpoint, linear endpoint, and interior scaled ridge atoms separately, retaining the `f(0)` contribution for selected zero directions. `CompactLoewnerTransfer` integrates these inequalities using the actual frozen nuclear norm and the exact optimal-tail identity. `RidgeTransfer` discharges the explicit compression premise of `RidgeTransferConditional` using `RidgeCompression`, whose eigenvector and positive-part bounds apply to singular PSD compressions without an inverse of the compression. The ridge transfer treats zero optimal tail separately: the approximation hypothesis forces `A` to equal the selected truncation of `Ahat`, then the ridge error vanishes. For positive tail, the source's inequalities (8)–(18) feed `ConstantElevenArithmetic`: `5g e₀ + g r`, `e₀ ≤ e + r`, and `r ≤ e` give exactly `11g e`; the tail estimate then gives the required factor `1 + 11ε`. I found no added matrix ordering, commutation, spectral-gap, invertibility, positive-tail, or `f(0)=0` premise in the final path.

`SelectedSpectralNuclear` derives the tail identity from the literal singular-value sum in each supplied orthonormal basis. `SpectralFunctionalCalculus` proves full function-matrix independence of the selected basis, including repeated eigenvalues. The analytic monotonicity bridge uses proved divided-difference, compression, and finite-spectral-crossing lemmas rather than an assumed Löwner representation. A scan of the RA-10 proof sources found no source-level `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, or `native_decide` declaration.

## Mechanical evidence and limits

I inspected the retained 3,044-job macOS build log at `docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/build.log` (SHA-256 `bdeaf93f0607977c5e61f34381dfadfdb1123f359b962a2caa9cba5d001e886f`). It records a successful build and prints only `propext`, `Classical.choice`, and `Quot.sound` for `admissibleFunction_hasCompactLoewnerRepresentation`, `transferBound_eleven`, and `ra10_target`; the source also invokes LeanCert `#assert_trust kernel`. This is historical local evidence, not the wrapper's isolated Linux result.

I independently ran the project selector against `origin/main`; it selected RA-10 alone. In PR #359 at head `5c7d6fe9`, the `select` CI jobs had succeeded and `verify (RA-10, randomized-and-low-rank-approximation/RA-10/lean)` was **in progress** when inspected. No successful `comparator-accepted` receipt or `lean_cert_proof_trust: kernel-checked` result was available then. I did not rerun Lean locally because this checkout had no Lean/Lake installation. A local `validate_manifest.py` attempt stopped before validation because this environment lacks Python `jsonschema`; the PR's Linux job must perform that check.

This review checks target meaning, the wrapper's link to immutable proof bytes, the critical proof graph and exact numerical assembly. It does not manually rederive every tactic step in the roughly 11,000-line source library, independently rerun the full build, or replace the fresh Linux Comparator and kernel checks. The independent proof reviewers and mechanical gate must all be evaluated on the final PR revision before any `Lean verified` promotion.
