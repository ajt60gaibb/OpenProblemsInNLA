# RA-08 independent statement referee 1

**Verdict: APPROVE the frozen statement boundary.** This approves fidelity and the proposed mathematical contracts, not their fourteen admitted proofs. Implementation, two independent final proof reviews, actual Linux verification, Comparator, default-kernel replay and operational acceptance remain outstanding. The canonical status remains `Solved`.

Reviewer: `/root/solved_statement_inventory`, an OpenAI Codex AI agent. Review completed on 12 September 2026 in America/New_York, with fresh commands recorded at 01:02 UTC on 13 September. I did not author the candidate definitions, statements or polynomial proof route. I gave early semantic review feedback, independently read the sources and performed the checks below. I did not use the other statement referee's report to establish this verdict. The coordinator's compression proof-route contribution is disclosed in the frozen package; it must be considered when selecting independent **final proof** referees.

## Exact reviewed boundary

The source base is `5830ed4fb06da0659414a3deb2a40ad327aca052`. I independently matched all 39 frozen project inputs and all ten original source files against both their recorded SHA-256 values and the actual base Git blobs before and after my checks. No frozen byte was changed.

| Input | SHA-256 |
| --- | --- |
| `reviews/statement-freeze.json` | `eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332` |
| `NLA/RA08/Definitions.lean` | `8c2f3a76e44730b1f9d5bc8e896070c10868bae817d0c3d11ace22b3c7d94c41` |
| `Challenge.lean` | `6dfe1fe49431bd3f5dc4c91360911d02c6aaf73d902a40fcabec79155fb11c18` |
| `NUMERICAL_TARGETS.md` | `a1fa22ee4cf7b3481795e68f9b04217b4da9761e3adb60c9cb3551ad2e4a1148` |
| `SourceCorrespondence.md` | `97b3f10eb986284804bbabee83deccbbfbfacb6b8b208e531917e082c2ae4c30` |
| `comparator.json` | `833d78dcda61a6d240fb1c50dd419ba7f95c3a8ddda768b7e1de6a0047359951` |
| `formalization.yaml` | `9ca52885b2ebfd85c2d4eba626d290fb93c2fff47287c2aff490123771be9c52` |
| `lake-manifest.json` | `9a2668eec65cda304be557e5984bbb155510433bdd0d506c01df050938a902c7` |
| `lakefile.toml` | `b874183e5fc45415bffa8be69c128049e3d9d80ccb9070f3c870bc2267d38ea6` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The complete frozen inventory and my final original-source/Git checks are retained in `statement-referee-1-evidence/final-input-audit.json`. I read the complete canonical target, authored manuscript, reviewed original manuscript, common preamble, prior informal review, submission documentation, definitions, all fourteen Challenge signatures, numerical targets and source correspondence. The mathematical body between the authored manuscript's explicit reviewed-body markers equals the complete reviewed body after `\maketitle`, including its `\end{document}`. The authored publication/review notice lies outside those markers and is preserved separately.

## Fidelity and mathematical assessment

The proposition preserves the original real problem: all dimensions `n ≥ 2`, ranks `1 ≤ k < n`, real PSD matrices `Ahat ≤ A`, nonnegative epsilon and continuous, nonnegative, nondecreasing, concave functions on `[0,∞)`. There is no generic assumption `f(0)=0`, global continuity, strict monotonicity or operator monotonicity. Representing a half-line function by a real extension introduces no restriction: every admissibility condition is on that half-line, and actual CFC extension invariance is a separate conclusion.

`spectralNorm` is the norm of the actual `Matrix.toEuclideanCLM` on Euclidean space. Fresh full elaboration exposes `ContinuousLinearMap.hasOpNorm`, `EuclideanSpace Real (Fin n)` and `WithLp 2`; it is not a default matrix entry or row norm. The order elaborates to the PSD-difference matrix order. Orthogonality is genuine `Matrix.unitaryGroup` over the reals, and natural matrix powers elaborate through `Matrix.semiring`.

`OrderedSpectralData` contains a full orthogonal reconstruction, decreasing nonnegative eigenvalues and actual matrix equality. The universal statement quantifies over **every** permitted data choice, including repeated-eigenvalue choices. Original and function truncations share the selected eigenbasis; discarded entries are zero, even if `f(0)>0`. The target is not silently replaced by `f(A_k)` or an independently rotated truncation. `orderedSpectral_exists` prevents a vacuous restriction to unavailable data, while `orderedSpectral_semantics`, `functionalCalculus_spectral` and `spectral_tail_norms` expose the actual eigenvector, CFC and norm obligations. Auxiliary zero-dimensional and rank-zero cases are retained where their signatures allow them.

The generic CFC contract for bare functions is mathematically sound in finite dimension: the actual Hermitian matrix spectrum is finite. I inspected the pinned construction and `Matrix.IsHermitian.cfc_eq`, which explicitly handles bare functions. Agreement with **every** ordered basis still needs proof. The scalar minorant is used pointwise on one matrix's proved spectrum through `cfc_mono`; no operator-monotonicity assertion about `min(x,1)` is smuggled into an assumption.

The fixed witness remains the original six-dimensional pair, `k=3`, epsilon zero, `t=1/65536`, `a=17/16`, `b=127/128`, and `f(x)=min(x,1)`. The source projection, approximation and vector are unchanged. The new polynomial

`h(x) = x − (67108864/1896129) x²(x−1/2)²(x−127/128)²`

replaces the source's contour remainder proof. It provides a weaker strictly positive gap, which is enough to negate the full original universal implication. The stronger source ratio, Nyström identity and nuclear or strictly-increasing extensions are not claimed by these exports. This is an explicit proof-route adaptation, not a replacement mathematical target.

The full spectral gap is a conclusion in `witness_spectral_location`. The proposed compression argument is sound: removing coordinate index 2 gives a compression bounded above by `(b+t)I < I`, while the remaining diagonal is at least `a`. For an actual eigenvalue `1 < λ < a`, the block eigenvector equations imply a positive quadratic form equals `(λ−α)u² ≤ 0`, forcing both components to vanish. The proof must still derive those equations from an actual eigenvector and prove the compression bound. Neither assertion is supplied as a target assumption.

The exact fourth eigenvalue, optimal spectral tails and basis-independent witness truncations are also conclusions, in `witness_tail_data`. They are not inferred in Lean from a decimal eigenvalue list. `operator_rayleigh_bound` states the actual generic Euclidean inequality, valid without a PSD assumption. The final two exports require an actual violating pair for every permitted witness basis and then an unconditional negation of the complete canonical proposition. There is no hidden finite-only substitute, added numerical premise or conclusion encoded in an opaque surrogate definition.

## Independent exact checks and fresh elaboration

My `reconstruct_exact.py` uses standard-library `Fraction` and a restricted parser of the actual definition literals. It does not import the author's checker. I independently reconstructed the source block projection from `U`, verified its flattened entries, symmetry, projection/complement identities, positive exact LDL pivots for the witness, and positive exact LDL pivots for the complementary compression's upper-bound difference. I verified the isolated sixth-coordinate eigenvalue `t`, the three matrix-vector products for `K(A)w`, their squared norm, and the independent double-application consistency check.

The exact independent values include

- `wᵀw = 26` and `wᵀFw = 14912/585`;
- `‖K(A)w‖² = 1800760572753083906132034496291 / 1019907849866242673982515970048000`;
- the positive relative gap `78605142319958855341529309 / 11432529876841442781954048000`;
- the exact identity `wᵀ(H(A)−f(Ahat))w = 26t(1+gap)`;
- the coefficients of `1−h(a+z)`: zero constant term followed by `19/17`, `537952/23409`, `2069504/23409`, `288428032/1896129`, `227540992/1896129`, `67108864/1896129`, all positive.

These are diagnostic computations, not a proof oracle for the future solution or evidence of a generic theorem. The scalar polynomial sign, actual spectrum, CFC order, eigenvalue ordering and all norm identities must be proved in Lean. The sole planned LeanCert numerical certificate is the strict positive rational gap on a singleton; its actual kernel-checked term must materially feed the Rayleigh contradiction and full negation. No interval or point certificate has been proved at this stage.

I freshly compiled `Definitions`, `Challenge` and my independent `Inspect` source into a newly created, separate prefix, excluding every previous project object. All three commands passed (6.93, 3.09 and 6.01 seconds). There were exactly fourteen intentional Challenge warnings and no warnings from Definitions or the inspector. The inspector printed all fourteen actual signatures and eight **definition-only** `#assert_trust kernel`/`#print axioms` pairs. Each of those eight closures uses exactly `propext`, `Classical.choice`, `Quot.sound`. No admitted Challenge theorem was used as a proof or certified by those checks.

This was macOS Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using ten clean pinned MI-22 dependency artifacts read-only. Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`. Every dependency source revision and cleanliness check passed before and after. No dependency build, cache copy, download or Linux execution occurred. Exact commands, paths, timestamps, source snapshots and raw logs are retained in `fresh-checks.json`; the inspector log hashes to `2c7bd1e3a104a1eb4383662aeeaecce9e3eb16b86262bb74d3f5b7c7b33a302d`.

The raw v0.4 schema passed. Its fourteen alignment declarations equal the exact Challenge and Comparator lists, with no definition exceptions and only the standard three permitted axioms. Metadata correctly reports no completed results; the repository's completion-only validator is therefore intentionally inapplicable. Neither `Proof.lean` nor `Solution.lean` exists. Postcheck parser corrections for source wrappers, Lean's backtick/universe printing and the retained Tau Ceti source snapshot are documented with preserved scripts; none changed candidate bytes or affected the three successful fresh compilations.

## Adapted Tau Ceti angles and remaining gates

I read all twelve rubric files at the retained Tau Ceti commit `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` and applied the repository's `docs/lean/REVIEW.md`. Actual rubric bytes were independently matched to retained GitHub tree blob IDs. API and rubric input hashes are recorded in `actual-api-rubric-inputs.json`; this is not an official Tau Ceti service run or endorsement.

| Angle | Statement-stage assessment |
| --- | --- |
| Correctness and scope | Full original real target and all fourteen obligations are faithful; no blocking mathematical finding. |
| Proof quality | Pending implementation. The exact polynomial/three-matvec route is auditable and substantially reduces computation. The genuine bridges above remain mandatory. |
| Reuse | Actual Mathlib spectral, finite CFC, PSD, unitary and Euclidean-norm APIs were checked; no external theorem is added as an axiom. |
| Generality | All original dimensions, functions, parameters and eigenbasis choices remain. Auxiliary contracts retain their stated degenerate cases. |
| API and naming | Definitions and signatures are isolated from proofs, names are scoped to `NLA.RA08`, and the source-to-export map is explicit. |
| Placement | The unchanged permanent RA-08 path is retained; no shared harness or unrelated canonical file changed. |
| Documentation | Numerical targets precede proofs; historical statement-stage metadata is truthful. It must be archived/refreshed when implementation status changes. |
| Attribution | Matthew J. Colbrook retains the mathematical result; Persson, Meyer and Musco retain the original question. George Stepaniants receives formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No email is published. |

No source correction is requested. Approval is limited to the exact hashes above. The parent must accept both independent statement reports before proof implementation starts; eventual final mathematical referees must be independent of all implementation contributors. No canonical promotion or publication is justified by this report alone.
