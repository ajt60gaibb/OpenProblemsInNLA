# IE-14 independent complete-source review — referee 1

**Verdict: APPROVE the complete mathematical source and local kernel checks at the exact candidate below. Authoritative Linux/Comparator verification remains pending.**

Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review`, independent non-implementing AI referee, 15 September 2026. I wrote no problem proof or specification. My only project additions are this report and its compact verification evidence. The review applies the repository's [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md); it is not external human review or official Tau Ceti endorsement.

## 1. Exact review boundary and previous finding

Candidate commit: **`c04371f6005220866f4f069809002d319554e039`**. The complete [23-input source seal](final-source-inputs.json) has SHA256 **`eba95af5ab465c97c346eecd5b5427ecb72c16a80d549fe85b1af799c566b54b`**. Every sealed file matches its committed blob, current bytes and, for the mathematical inputs, my independently compiled snapshot. The commit's immediate parent is the approved pre-proof boundary `58b516b6dbb7fa4e885b679d261bf779c263aad4`; all ten frozen inputs and both independent statement approvals remain exact.

I read the entire canonical target, complete packaged manuscript, historical review, numerical dossier, all twelve `NLA/IE14` modules, Challenge, Solution, README, metadata and retained contributor package. The complete original source hashes, 217-ID registry and published existing verifications remain unchanged relative to `d8c38a795876b132c90df8d1be8682d3dcde394c`. IE-14 retains its canonical path and **Solved** status. The manuscript's older quoted source digest is correctly distinguished from the complete packaged TeX hash `4c20c2c20e6d05945911883682bc823096ef0ff1011cbd31bf941fd1f309b869`.

My preliminary review caught an unused-simp cleanup regression in `factorIndex_injective`. The coordinator repaired the missing coercion reduction, together with the related Tail/WitnessEntries reductions, and made the strict half helper's use of its certificate explicit. I read those exact differences and rebuilt the repaired complete source independently. It now succeeds with **zero warnings**. The [historical finding](../verification/final-source-referee-1/superseded-preliminary-review.md), failing log and [repair diff](../verification/final-source-referee-1/repaired-helper-diff.patch) remain in evidence; the successful final checks supersede that earlier compilation failure. No unresolved mathematical or compilation finding remains.

## 2. Complete original-target correspondence

The proved result is the original all-orders extremum: for **every n≥4**, the greatest permitted growth over all nonsingular **complex** cyclic tridiagonal matrices with **both corners nonzero**, and over **every maximal-modulus GEPP tie path**, is `F_(n+1)+1`. Every entry of all n active matrices is covered, including the original input and final scalar. No symmetry, reality, diagonal dominance, genericity, deterministic tie rule or preliminary reordering is imposed.

| Reviewed public export | Actual proof and complete scope |
| --- | --- |
| `numerical_bounds` | Explicit kernel-certified conjunction `0<1/2` and `1/2≤1`, consumed in witness pivots and normalization. |
| `entryMax_semantics` | Actual finite maximum of complex entry moduli, with nonnegativity, every-entry bound and attained index pair for n≥1. Implemented directly in Basic. |
| `admissible_path_exists` | Every nonsingular complex square matrix has a full literal GEPP path, independently of cyclic sparsity. The n=0 case is the harmless empty path. |
| `all_active_entries_bound` | Every active i,j at every k on every admissible path obeys `(F_(n+1)+1) * entryMax A`. |
| `witness_data` | The frozen all-size rational input is nonsingular, has exactly the required support allowance, both actual nonzero corners and entry maximum one. |
| `witness_attainment` | The frozen physical current-last-row path is legal at every stage and its full-history growth equals the bound. |
| `canonical_result` | Actual `IsGreatest` membership and universal upper bound, followed by equality of the real supremum with the attained value. |

I separately loaded Challenge and Solution and printed each declaration's fully elaborated Lean `Expr` type. The **seven complete type representations are byte-identical**. This includes all binder types, dimensions, quantifiers, predicates and referenced mathematical definitions. It is an independent local correspondence check; it is not relabelled as the future sandboxed Comparator run.

## 3. Actual proof audit

**GEPP and nonvacuity.** Supported-vector active-block injectivity is initially obtained from actual determinant nonzeroness. A vector in a Schur kernel is extended by a pivot coordinate and contradicts the previous active injectivity. The proof never asserts that a zero-padded whole matrix stays nonsingular. A nonzero active column and finite maximum selection give the next pivot and then a complete path. This establishes nonemptiness without narrowing the public all-tie family. Actual complex norms bound every multiplier by one.

**Physical labels and universal front.** `origin` composes the actual row transpositions in the correct order. `FrontInvariant` proves active/distinct old rows, their original labels, complete coverage and unchanged entries of every later original row. A nonzero admissible pivot must lie in the old-old-fresh front because all other actual original pivot-column entries vanish. The advancement theorem proves survivor and fresh-row bookkeeping from the literal Schur recurrence. These are proved intermediate invariants, not additional input hypotheses.

**All column histories and endpoints.** The three possible removed rows give the exact maximum/sum estimates `M′≤max(T,M+c)` and `T′≤T+c+max(M,c)`. They do not assume the chosen pivot maximizes the target-column entry. With zero fresh entry, `M′≤T` and `T′≤T+M` drive the Fibonacci induction. The last column has n−3 zero-fresh updates, then a bounded fresh entry, giving survivor sum `(F_(n+1)+1)E`; the final scalar is bounded separately by those two survivors. The penultimate column has n−4 zero-fresh updates and two bounded arrivals, giving the sufficient `(F_(n−1)+1)E` bound. First/second/middle columns have their complete active histories bounded by E or 2E. Future rows retain input entries bounded by E. The final theorem exhausts every active j and handles k=n−1 separately. At n=4 the middle interval is empty and the penultimate zero-run has length zero, with no negative Fibonacci index.

**Witness structure and actual trajectory.** Unit-lower and upper triangular determinant facts prove LU nonsingular; a genuine finite row permutation preserves determinant nonzeroness. Separate column identities prove all forbidden entries zero, corner values exactly 1 and −1, and entry maximum one. `stageFactor_swap_succ` describes actual physical swaps; `witness_trajectory` proves the full active trailing-product identity by induction from the frozen input. Nonzero upper diagonal entries justify cancellation, and lower-factor moduli at most one justify maximality of every selected pivot. The final scalar is exactly `F_(n+1)+1`. No pre-permuted LU run is substituted for the canonical GEPP run.

**Growth and greatest value.** The first actual nonzero pivot proves the denominator `entryMax A` positive. The all-entry bound yields the finite peak/growth upper bound. The normalized witness and its actual final scalar supply the matching lower bound. `IsGreatest` explicitly constructs membership and bounds every element of the complete growth set. Its resulting least-upper-bound property justifies `csSup_eq` with nonemptiness; no empty-set or unbounded-supremum convention is used.

**Consumed numerical proof.** Both interval calls explicitly use `trust := kernel`. The strict component is passed through the actual complex half norm into pivot/determinant nonzeroness; the upper component bounds positive and negative half input entries. I independently traversed actual compiled theorem expressions, including types and proof values, to the named certificate. It is present in the public `witness_data`, `witness_attainment` and `canonical_result` closures (**106, 341 and 344 project constants**, respectively), and in each half helper. It is not a detached decorative certificate. All matrix dimensions, sparsity arguments, Fibonacci identities and trajectory steps remain symbolic.

## 4. Independent compilation and exact diagnostics

My project snapshot began with its own empty project build directory and shared only the exact pinned dependency package/cache tree. I verified every dependency Git revision and absence of modified tracked dependency source. Actual compiler: Lean **4.33.1**, `arm64-apple-darwin24.6.0`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`.

- Fresh Challenge: **3,008 jobs**, exactly seven intentional specification holes.
- Fresh Solution: **3,642 jobs**, every project module built, **zero warnings** and no proof holes.
- Independent `#assert_trust kernel` and transitive axiom reports for **all 98 project theorem declarations**: only `propext`, `Classical.choice`, `Quot.sound` permitted. Every public closure has precisely those three.
- Seven fully elaborated expected/actual types: byte-identical.
- Metadata schema and seven-export coverage: pass. Solution imports Proof and never imports Challenge; no definition holes are configured.

My separate exact Fraction/Gaussian-rational diagnostics passed **10,878 checks** across 80 complex cyclic samples in dimensions 4…8, **1,059 physical-front states**, **979 admissible tie edges**, and complete active witness-tail identities in dimensions 4…12. They check the original-label invariant, every per-column envelope, actual final scalar and smallest-order boundary. Sums of two complex moduli are compared exactly by nonnegative squared inequalities, not floating-point tolerance. I also replayed the contributor's independent rational checker for all 27 witnesses n=4…30; its result and full source-hash records match the frozen records byte-for-byte. These finite diagnostics corroborate conventions and arithmetic; they do not replace the universal Lean proof.

The earlier preliminary proof closure checks and final corrected checks are distinguished in retained evidence. I did not execute Linux, Comparator or an external kernel in this review.

## 5. Proof quality, reuse, API, documentation and attribution

The proof applies pinned Mathlib finite-maximum, complex-norm, matrix-injectivity, triangular-determinant, permutation, Fibonacci and supremum APIs directly. I inspected relevant definitions/signatures and compared existing IE-05 GEPP and LU-trajectory proofs. Their complex adaptation is acknowledged; the new actual-swap and original-label front arguments are not assumed from the real or rook-pivoting developments. The actual `det_permute` type is used on rows despite its upstream docstring wording. The pinned Forsythe/Schiffer structure/API references are identified accurately.

The maximum/sum formulation avoids unnecessary sorting; carrying E avoids a separate scale-invariance construction; supported-vector injectivity avoids dependent active-matrix dimensions; triangular products avoid expanded determinants. These reductions preserve the target. Generality and degenerate dimensions are explicit. The module split, theorem names and small public wrappers keep the seven reviewed statements identifiable; the direct Basic implementation of `entryMax_semantics` is documented. No new architecture or theorem weakening is requested.

README and metadata truthfully describe a completed **local candidate**, while final source and Linux/operational gates are historically pending at candidate preparation. They disclose intentional Challenge holes, local dependency-cache use and original attribution, and make no canonical Lean-verified claim. George Stepaniants has the requested **Department of Computing and Mathematical Sciences, California Institute of Technology** affiliation; Matthew J. Colbrook retains original resolution credit and Cambridge affiliation. Substantial AI assistance and independent non-implementing reviewer roles are disclosed, with no added contact email or author endorsement claim.

I checked the contributor evidence package, all current checksums, source snapshots and renamed `.trace.json` payloads against the retained original checksums. The README packaging note is the sole intentional original README addition; removing it recovers the original digest. These logs are correctly labelled contributor development evidence, including historical failed attempts, rather than independent approval.

These findings cover the repository's Tau Ceti adaptation criteria: correctness, scope, proof quality, reuse, generality, API design, naming, placement, documentation and attribution.

## 6. Exact source seal and evidence

| Candidate input | SHA256 |
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

The compact [independent verification archive](../verification/final-source-referee-1/SHA256SUMS) retains my audit script/result, actual build/type/trust logs, reviewer check sources, exact diagnostics, source-hash records and superseded finding/repair evidence. It duplicates no project build artifacts or dependency tree. [The audit record](../verification/final-source-referee-1/audit.json) records **357 successful source/pin/review checks**, the 23 candidate hashes, all ten frozen hashes, original source context, 98 axiom closures and actual certificate dependencies.

Audit JSON SHA256: `bbc8e50c6dd3045f1524b687a2152286cc082921beea84e5bb91d5b2d9df74f4`.  
Verification checksum-list SHA256: `bffe4ebd28013598c7ef640ff53fdd6852134998bf398d3e7281f16ef1c71bd3`.

**Final disposition: APPROVE these exact mathematical source bytes and local kernel checks.** No source correction remains. Canonical status promotion requires the actual pinned Linux Comparator/default-kernel run and controls, plus both independent operational audits. This source review performs none of those later gates and makes no new literature, priority, human-review or official-endorsement claim.
