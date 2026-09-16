# IE-14 independent final complete-source review — referee 2

**Verdict: PASS for the exact complete source candidate.** No substantive fidelity, correctness, or trust defect remains in this review. This is a source-review approval, not a claim that Linux Comparator verification, operational review, publication, or canonical promotion has occurred.

**Reviewer:** OpenAI Codex AI agent `/root/existing_verification_audit`, independent referee 2. I contributed no IE-14 definitions, certificates, proof implementation, or mathematical source edits. I applied the repository [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md), covering fidelity/scope, correctness/proof quality, reuse/API, documentation and attribution. This is not external human review or official Tau Ceti endorsement.

**Candidate:** `c04371f6005220866f4f069809002d319554e039`; published source base `d8c38a795876b132c90df8d1be8682d3dcde394c`; pre-proof boundary `58b516b6dbb7fa4e885b679d261bf779c263aad4`. The [23-input seal](final-source-inputs.json) has SHA-256 `eba95af5ab465c97c346eecd5b5427ecb72c16a80d549fe85b1af799c566b54b`.

## What I independently inspected and reproduced

I read the complete canonical README, complete retained Colbrook manuscript and historical source context, frozen Definitions, all seven Challenge signatures, the complete numerical dossier, all twelve NLA modules, Solution, Comparator configuration, pins, README and formalization metadata. I compared the actual proof arguments to the full original target rather than relying on contributor PASS messages.

All 23 candidate inputs match both the submitted hashes and Git candidate blobs. All ten pre-proof inputs match the frozen bytes and boundary commit. Both sealed pre-proof reports remain unchanged. All seven complete original source files match their recorded hashes, candidate Git and published base; the permanent IE-14 registry path is unchanged. Current canonical status is **Solved**.

I built a separate source snapshot with fresh project `.lake` outputs, copying seventeen source/configuration files. Its `.lake/packages` link reused pinned dependency checkouts and their cached artifacts; I checked all ten dependency Git revisions and clean tracked contents against the manifest. The pinned Lean binary reports 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, arm64 macOS.

Own `lake build Challenge Solution` completed successfully: **3644 jobs**, exactly seven expected specification-only Challenge `sorry` warnings, and no Solution warnings. A separate audit issued `#assert_trust kernel` and `#print axioms` for **all 98 project theorem declarations**; every command succeeded and every transitive axiom set is contained in `propext`, `Classical.choice`, `Quot.sound`. The implemented import closure has no Challenge import or source `sorry`, `admit`, `native_decide`, or custom `axiom` token.

Separate processes imported Challenge and Solution and printed all seven public types with `pp.all`; the output files are **byte-identical**. This is independent local exact-type evidence, not a substitute for the required actual Lean4 Comparator/default-kernel run. The schema/coverage validator also passed all seven declarations. I replayed the frozen standard-library Fraction diagnostics for all 27 witnesses, `4≤n≤30`; output is byte-identical. Those checks supplement, and do not establish, the universal proof.

Initial reviewer-only audit files used an unsupported pretty-printer option and incorrect `unless` syntax. I corrected only scratch audit code, retained both failed initial logs, and reran successfully. These were not candidate errors.

## Complete-target correspondence and mathematical audit

### Actual algorithm, domains, ties and maxima

`Mat n` is genuinely complex. `rowSwap` permutes physical rows only, and `trajectory 0=A`; there is no preliminary reordering of a run. `schurStep` uses the literal nonzero pivot and trailing update, padding only discarded positions with zero. `AdmissiblePivot` permits every active maximal-modulus tie and requires its pivot nonzero. `CyclicInput` requires nonsingularity, exactly the permitted support condition, and both actual corner entries nonzero; ordinary band entries may vanish. No reality, genericity, conditioning or sign hypothesis is introduced.

The finite NNReal supremum definitions are actual entrywise modulus maxima. `entryMax_semantics` proves both the upper bound and existence of a maximizing entry for `n≥1`. Active maxima restrict both indices; the growth numerator includes the original input, every active Schur complement and final scalar. It excludes only the subsequent empty padded matrix. Dividing by the entry maximum is justified by positivity from an actual admissible initial pivot.

`GEPP` proves nonvacuity for every nonsingular complex square input through injectivity on vectors supported in the genuine active block. It does not incorrectly assume that a zero-padded eliminated matrix remains nonsingular. A nonzero active column follows from applying that injectivity to a basis vector; finite maximization selects a nonzero largest-modulus pivot. Injectivity survives the physical swap and a Schur kernel-vector lift with its nonzero divisor. The recursively chosen trajectory agrees with the literal trajectory. Dimension zero in the separate existence export is correctly the empty path; the canonical sharp result always assumes `n≥4`.

### Full upper bound, including the small-dimension boundary

`Front` derives the original-label permutation and two-old/one-fresh invariant from actual swaps, original sparsity and nonzero pivot admissibility. It establishes that unentered future rows stay active and retain their original active entries. The pivot belongs to the three-row front because all other active pivot-column entries are zero. This invariant is proved, never assumed in the public target.

`FrontBounds` treats all three possible removed rows; it does not assume the pivot is largest in an unrelated target column. Complex modulus, the triangle inequality, and the actual multiplier bound give the old-pair maximum/sum updates. For a zero fresh entry these are `M′≤T` and `T′≤T+M`; the general fresh bound is handled separately. `ColumnBounds` then proves every column history symbolically: first, second, middle, penultimate and last. The last-column Fibonacci recurrence has its actual fresh-entry transition, the penultimate column handles `n=4` with a zero-length initial run, and the final two-row step explicitly bounds the scalar. The final index partition covers every stage and every active row and column. The result is the unnormalized bound `(F_(n+1)+1)*entryMax A`, so no unproved invariance of paths under normalization is needed.

### All-size witness, actual physical path and attained supremum

The literal lower and upper factors, finite row assignment, rational halves and integer Fibonacci entries define the advertised rational witness for every `n≥4`. Triangular diagonal-product arguments prove the factors' determinant nonzero, and the actual row permutation preserves nonvanishing. `WitnessEntries` expands the full product and handles nonfinal ordinary columns, the exceptional second column, and last-column Fibonacci cancellation. This proves every forbidden entry zero, both corners explicitly nonzero, all entry moduli at most one, and an actual corner of modulus one.

`Tail` proves the trailing-product identity in physical coordinates. The stage-factor map and actual swap update show that the path first keeps row zero and then selects the current last row, realizing original order `(1,n,2,…,n−1)` without changing `trajectory 0`. Every divisor is proved nonzero. The multiplier/factor norm bounds establish that the selected entry is an allowed maximum even in ties. The final scalar is exactly `F_(n+1)+1`. Combining its lower bound with the universal active-entry bound gives equality of the entire growth, not merely a selected final pivot.

`Attainment` constructs an actual member of `cyclicGrowthSet n`, proves the universal upper bound, and obtains `IsGreatest`. Its real-supremum equality follows through `IsLUB.csSup_eq` with explicit nonemptiness from that member. Neither empty-set nor unbounded-supremum conventions can supply the canonical result. Together, these arguments settle all dimensions and all admissible complex inputs/paths in the original target.

### LeanCert consumption and trust

`half_bounds_certificate` proves both `0<(1/2:ℝ)` and `(1/2:ℝ)≤1` with explicit `interval_decide (trust := kernel)` and kernel trust policy. I inspected the compiled helper proofs: `half_complex_ne_zero` uses the conjunction's **left** projection; `norm_half_complex_le_one` uses its **right** projection. The former supports nonzero upper pivots and determinant/path legality; the latter supports normalization of the input entries.

An independent traversal of compiled constant types and opaque theorem values confirms that **both helpers and the certificate** occur in the actual project dependency closures of `witness_data` (106 constants), `witness_attainment` (341), and `canonical_result` (344). Thus the numeric certificate is consumed in the complete target. The proof of unbounded dimensions, complex front geometry and Fibonacci recurrence remains symbolic; no finite diagnostic or certificate replaces it.

## Reuse, API, documentation and attribution

The development reuses pinned Mathlib finite maxima, complex norms, matrix injectivity/determinants, triangular products, finite permutations, Fibonacci identities and conditional-supremum facts. I checked the existing IE-05 supported-vector GEPP and trailing-LU-sum patterns; their adaptation to complex data and this actual row path is credited. No real GEPP or rook-pivoting theorem is silently used as a cyclic complex bound. Problem-specific front and witness definitions are confined to `NLA.IE14`, with the frozen semantic API clearly separated from proofs. The imported broad tactic module is not an additional mathematical assumption.

The README and YAML accurately describe a complete local candidate with final source/operational gates pending. The frozen Challenge remains the default target and its intentional holes are explicitly separated from Solution's zero proof-hole count. All seven metadata declarations/configured names agree. George Stepaniants's full requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation is present, no contact email is introduced, and Matthew J. Colbrook's original proof authorship and Cambridge affiliation remain preserved. Substantial Codex assistance, contributors, independent AI reviewers, licenses, structure/API references and lack of external endorsement are disclosed truthfully.

No blocking source change is requested. Later promotion must still use the actual pinned Linux Comparator, default kernel replay, permitted-axiom audit, sandbox and rejection controls, followed by independent operational reviews. This report does not attest those future gates.

## Exact candidate hashes

| Input | SHA-256 |
| --- | --- |
| `.gitignore` | `3b8ef443f22e1029ffe4683cc0b3950064f9559bba9b202d604e658bd3370bf6` |
| `Challenge.lean` | `5c5dedb2af797037b78490d7b0f353fb876e06f214f5dcaac8116fcb24419819` |
| `LICENSE` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `NLA/IE14/Attainment.lean` | `a55a77c4b5f5174468893a85dab5d47bb8cb11e9e4cff38db7cd46b086c7698f` |
| `NLA/IE14/Basic.lean` | `f75c6ae2c7d5532afc827e4405297ce8567332ade91a74a0df7f1284f1022a6b` |
| `NLA/IE14/Certificates.lean` | `be7f06f647851c46f5acb703f14e818058b97e592d8a6556b79c2a64ec9f5c33` |
| `NLA/IE14/ColumnBounds.lean` | `2ceaa43f8ec65e9508b6baf2f3a119b649a37274a7b6d1b076ed06a2e79e782b` |
| `NLA/IE14/Definitions.lean` | `fbc915432bf9b254d966e73af7ad3c525dfff44f11c1ec420a041a94817b5d91` |
| `NLA/IE14/Factors.lean` | `f166d5ff22ab7e7218545ceefeffca09da14e7f0cb93ffdcd28122f23b39f465` |
| `NLA/IE14/Front.lean` | `6c72173fcf2274fff2f91429436994f30ea7a2976b3356ae4bd8c7e592beab71` |
| `NLA/IE14/FrontBounds.lean` | `384751a3ae156e27a0deaa45d180343ef06f2ce4fb74a27da9cea88d56dd6a4d` |
| `NLA/IE14/GEPP.lean` | `92f621550c134f82e130e80aa8a1fbc364ddc0f8e236149e5bc56383df33a18f` |
| `NLA/IE14/Proof.lean` | `4591b5808528b0f4546865d0de13559af934fe012e345ffe33642d3233cd3c82` |
| `NLA/IE14/Tail.lean` | `655c1d27a7d14975dc263501d8e950d8873c5f5bbaf6d14283ce8d83708acdd4` |
| `NLA/IE14/WitnessEntries.lean` | `674c896780e3a0c4ffe75e78a715fdd86a80516cd41fbb3d6b510abfde7755ba` |
| `NUMERICAL_TARGETS.md` | `14fd18ff66964f871e1d0d1c8b95a2b0cdfc23197637609b40e122f3ca9589e2` |
| `README.md` | `011ab9aefbed0a0cd4b12aaa67a0638153701c40261786489a3afdacaaf80a84` |
| `Solution.lean` | `14673360dbc0aae74dad047baf1a60ce4216ea8f288358ed2ab540fe87f8052a` |
| `comparator.json` | `56187f72be532ab0e2e61009ed7846827ffee25bf44585e98fb11e7816d35490` |
| `formalization.yaml` | `44d606586ffc138e452fc83a5b53463c1cb8105c656aa07013a32fca6c0f2872` |
| `lake-manifest.json` | `a53781cedceef565cf6dc798e453fdc8e265f2d288c4a997b3c2104e4a795315` |
| `lakefile.toml` | `f658ed03207a4dc271218fb6b02366938e58da52d75196d552490c3d1a827303` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

## Retained independent evidence

The [evidence summary](../verification/final-source-referee-2/review-evidence.json), [fresh build](../verification/final-source-referee-2/fresh-build.log), [98-theorem audit](../verification/final-source-referee-2/independent-trust-axioms.log), [literal Challenge types](../verification/final-source-referee-2/challenge-types.log), [literal Solution types](../verification/final-source-referee-2/solution-types.log), [compiled certificate audit](../verification/final-source-referee-2/certificate-dependency.log), and [input verification](../verification/final-source-referee-2/input-verification.json) record my own checks. Audit Lean/Python sources, pin records, frozen seals, diagnostics and initial reviewer-only error logs are retained beside them. [SHA256SUMS](../verification/final-source-referee-2/SHA256SUMS) seals every evidence file. No core source was modified or committed by this reviewer.
