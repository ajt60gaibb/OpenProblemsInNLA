# IE-14 independent pre-proof statement review — referee 1

**Verdict: APPROVE the exact ten submitted boundary inputs below.** The definitions, seven Challenge targets and complete dossier faithfully express the full canonical problem. The source argument and proposed proof simplifications are mathematically valid. No statement change is requested. This is **pre-proof approval only**: no target theorem, LeanCert certificate consumption, axiom closure, Comparator or Linux result has yet been established.

**Reviewer:** OpenAI GPT-6 Codex `/root/reference_api_review`, independent non-implementing AI referee. **Date:** 2026-09-15. I read the entire canonical README, complete retained manuscript and historical review, all definitions/signatures, final dossier, submitted checker/results/source hashes and pins. I wrote no IE-14 proof or specification code and edited only this report/evidence. Review follows [the repository's Tau Ceti adaptation](../../../../docs/lean/REVIEW.md), without external human review or official endorsement.

## 1. Complete-target fidelity and nonvacuity

The canonical target is the sharp GEPP growth **F_(n+1)+1 for every n≥4**, over all nonsingular complex cyclic tridiagonal matrices with **both nonzero corners**, all admissible maximal-modulus ties and all active entries. The given ordering is fixed before the run. It is not a real-only, deterministic-pivot, final-scalar-only or finite-dimension question.

The actual definitions preserve this scope:

- `Mat n` is the full complex matrix space. `CyclicPosition` is precisely the zero-based ordinary band plus the two corners; `CyclicInput` imposes determinant nonzero and vanishing outside that pattern, with no symmetry, dominance, sign or genericity assumption. Its corner quantifier identifies the actual first/last indices and is nonvacuous under n≥4.
- `trajectory A path 0 = A`. Each step performs the actual row transposition at current physical positions and the literal trailing Schur update. Columns are never permuted. `AdmissiblePivot` requires a nonzero pivot at or below the active first row and compares its modulus with every active pivot-column entry. Every maximal tie is permitted.
- Zero padding lies outside the new active block. `activeMaxNN` restricts both indices correctly. `growth` includes exactly the n active stages 0,…,n−1, counting the input and final scalar while excluding the subsequent empty padded stage. Finite NNReal suprema and real coercions give literal complex entrywise modulus maxima, not an operator norm.
- `all_active_entries_bound` quantifies every permitted path and every active triple k,i,j. The first nonzero pivot ensures `entryMax A>0`; a proof must establish that positivity before dividing.
- `admissible_path_exists` supplies an actual complete path for every nonsingular complex input. Its n=0 extension is harmless: the finite path domain and admissibility requirements are empty. `entryMax_semantics` correctly assumes n≥1 to export a maximizing entry.
- `cyclicGrowthSet` contains exactly values realized by genuine inputs and paths. `IsGreatest` exports both actual attainment and an upper bound, and the explicit `sSup` equality records the original sharp constant. Neither empty-set nor unbounded-set conventions can discharge this obligation. The joint supremum equals the original nested supremum; each nonsingular input has an admissible path.

All seven configured targets match their dossier descriptions: the consumed half-coefficient bounds; literal entrywise maximum semantics; nonempty full GEPP path family; universal all-active-entry bound; actual normalized cyclic witness; actual witness-path attainment; and the attained sharp constant plus supremum equality. No replaceable definition holes are configured.

## 2. Source proof, front bookkeeping and exact witness

I checked the source's two-old-row/fresh-row argument independently. Tracking **original labels through actual swaps** is essential: at each early step only two old surviving rows and the newly entering row can have a nonzero pivot-column entry. Later original rows remain unchanged because all earlier multipliers were zero. A nonzero chosen pivot must belong to that front, regardless of ties. This structural invariant is explicit future proof work, not an extra target hypothesis.

The dossier's alternative scalar bookkeeping is sound. For old maximum M and sum T, and fresh target magnitude at most c, choosing a fresh pivot gives survivor maximum ≤M+c and sum ≤T+2c; choosing either old pivot gives maximum ≤max(T,M+c) and sum ≤T+c+M. Therefore universally

`M′ ≤ max(T,M+c)`, `T′ ≤ T+c+max(M,c)`.

At c=0 these become `M′≤T`, `T′≤T+M`, since M≤T. This retains the source Fibonacci envelope without sorting at every step. It uses only complex triangle inequalities and multiplier modulus ≤1. A pivot row's zero entry in a *target* column is unrelated to its required nonzero elimination pivot.

I separately checked every column history in §4: column 1; column 2; middle columns; the next-to-last column starting from (1,0); and the last column starting from (1,1). The last column has exactly n−3 zero-fresh updates; the next-to-last has n−4. The boundary n=4 has one and zero such updates respectively, no negative Fibonacci index, and an empty middle-column range. Fresh entries, unentered rows and removed pivot-row values are all included at their proper active stages. Stopping each history when its column is eliminated avoids an extra spurious update. Carrying `entryMax A` as a common factor instead of separately normalizing the matrix is equivalent and does not change the target.

The witness lower/upper factors and the final-column branch order match the source. `factorIndex` is the inverse of the row labels (1,n,2,…,n−1), used **to define the input matrix**. `witnessPath` keeps row zero at step zero and thereafter selects the **current last physical row**. I checked that these successive swaps produce precisely the original-label sequence claimed; they do not perform a forbidden preliminary permutation.

The dossier's full tail-product invariant correctly uses factor labels `factorIndex i` at stage zero and, at later active stages k, label k at physical row n−1 and label i+1 elsewhere. The chosen pivot row has factor label k; upper triangularity gives the active pivot column as `L_(f_k(i),k) U_(k,k)`. Its designated pivot is nonzero and maximal. The Schur update removes exactly the kth tail contribution, with the physical swap producing the next label map. The final scalar and normalized whole-run growth equal the Fibonacci bound. The n=4 matrix, pivots (1,1/2,1,6), determinant 3 and both corners agree with independently recomputed arithmetic.

The path-existence plan correctly uses injectivity on vectors supported in the actual active block. It does **not** assert nonsingularity of the full padded trajectory, which has zero rows/columns after the first step. Nonsingularity of the witness is obtained from nonzero triangular diagonals and a row permutation, without an expanded determinant. The optional signed determinant formula is not substituted for any public target.

## 3. Numerical and API evidence actually executed

The proposed certificate is exactly `0 < (1/2:ℝ) ∧ (1/2:ℝ) ≤ 1`. The plan requires explicit LeanCert kernel mode, consuming the strict component to prove the half pivot nonzero and the upper component in the input half-entry norm bound. Real-to-complex coefficient/norm bridges and inclusion on the actual witness dependency path remain mandatory. This review approves that plan; it does not claim the certificate has run.

I independently copied the mathematical inputs into a fresh source snapshot with only pinned dependency-cache reuse. **Challenge compiled successfully: 3008 jobs and exactly seven intentional specification holes.** The final mathematical and pinned bytes are identical to that compiled snapshot. My no-proof [`BoundaryAudit.lean`](statement-referee-1-evidence/BoundaryAudit.lean) also compiled, printing the actual definitions and all seven types and checking finite maxima, sharp-supremum, determinant/Schur, Fibonacci and complex norm APIs. The actual compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; every dependency revision matches the manifest and all tracked dependency sources are clean.

My own independently authored Fraction/Gaussian-rational diagnostic code passed **1,652 exact checks**. It verifies the literal witness and current-position path for every n=4,…,30, every chosen pivot/active peak, full selected U rows, factor-column identities and label sequences; complex phase/scaling versions for n=4,…,9; and every admissible tie branch within 40 fixed small complex samples, giving **125 complete paths**. These finite samples do not prove the universal bound.

I then read the full contributor checker and independently replayed it: all 27 cases pass, with both generated numerical JSON and all seven complete-source hashes **byte-identical** to the submitted outputs. That checker additionally checks the entire active factor-residual matrix and independently computes the determinant using a different elimination routine. Its results agree with my independently produced growth values and pivot lists for all 27 orders. The two diagnostics have distinct authorship and scope; neither is a proof of an all-size/all-complex theorem.

Pinned Mathlib provides the appropriate finite suprema, complex norm, Fibonacci recurrence, triangular determinant, row-permutation and Schur-block APIs. I inspected those sources and the actual existing IE-05 GEPP/supported-vector and LU-tail proof patterns. Their real scalar specialization requires a genuine complex adaptation; IE-15's rook-pivot/column-swap semantics cannot replace this problem's GEPP. No ready universal cyclic-front theorem is presumed. Dossier naming and separation of frozen definitions, auxiliary plan and full public obligations are clear.

## 4. Original sources, attribution and stage truth

All seven recorded complete original files match published base `d8c38a795876b132c90df8d1be8682d3dcde394c`, and all 217 permanent IDs are unchanged. The original full manuscript is **7141 bytes**, SHA-256 `4c20c2c20e6d05945911883682bc823096ef0ff1011cbd31bf941fd1f309b869`. The dossier correctly distinguishes this packaged artifact from the older 5942-byte source digest quoted in the historical review; it does not silently trim or rewrite source text to equate them.

I independently consulted [Higham's original book, Problem 9.15(b), printed p.193/PDF p.222](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf#page=222): the pattern is tridiagonal except for both nonzero corners. The problem there omits a field; [Theorem 9.11, printed p.173/PDF p.202](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf#page=202) explicitly treats complex matrices. The canonical page supplies the retained all-tie/original-order convention. This is a direct source-alignment check, not an exhaustive literature or priority search.

Original Colbrook/Cambridge authorship and historical disclosures remain intact. Planned formalization credit is George Stepaniants, **Department of Computing and Mathematical Sciences, California Institute of Technology**, with AI assistance and no new contact email. The contributor dossier explicitly distinguishes its mathematical preparation from independent referee approval. Canonical status remains **Solved**; Solution imports only Definitions, and there are no implementation modules. The retained [preliminary review](statement-referee-1-evidence/preliminary-scope-review.md) is historical preparation, now completed by this exact-byte report.

## 5. Exact ten-input approval seal

The authoritative [statement submission](statement-submission.json) has SHA-256 `9adea8e22570a4da8c3b8363697e66651ebd015ab7828d18b50c74f7ee6598e6`. All ten hashes below match both the actual project and my independent snapshot:

| Project-relative boundary input | SHA-256 |
|---|---|
| `NLA/IE14/Definitions.lean` | `fbc915432bf9b254d966e73af7ad3c525dfff44f11c1ec420a041a94817b5d91` |
| `Challenge.lean` | `5c5dedb2af797037b78490d7b0f353fb876e06f214f5dcaac8116fcb24419819` |
| `NUMERICAL_TARGETS.md` | `14fd18ff66964f871e1d0d1c8b95a2b0cdfc23197637609b40e122f3ca9589e2` |
| `comparator.json` | `56187f72be532ab0e2e61009ed7846827ffee25bf44585e98fb11e7816d35490` |
| `lakefile.toml` | `f658ed03207a4dc271218fb6b02366938e58da52d75196d552490c3d1a827303` |
| `lake-manifest.json` | `a53781cedceef565cf6dc798e453fdc8e265f2d288c4a997b3c2104e4a795315` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial/exact-check.py` | `135da24ac7a60f0da83b82560bfa52b0beafde9e254bcb0ea98d4eb9eab371e2` |
| `reviews/initial/exact-results.json` | `4f1622f7e712b4726d162c107697913b0853d39b21c00701abc877a7ff0b6297` |
| `reviews/initial/source-hashes.json` | `be90e718a57673dddc1236b002c7ebc27e8e57a203ba41f5c090baa37bc59b22` |

The independent [audit JSON](statement-referee-1-evidence/audit.json) records **102 passing source/pin/semantic checks**, all source identities and dependency versions. The [evidence seal](statement-referee-1-evidence/SHA256SUMS) binds the executable audit, independent arithmetic, contributor replays, fresh compiler logs, no-proof API probe and historical preliminary note.

**Final pre-proof disposition: APPROVE these exact bytes.** The universal front/label induction, every all-orders witness identity, certificate consumption and all seven proofs remain implementation obligations. Final independent proof review, permitted-axiom closure, real Comparator/default-kernel verification, reproducible Linux execution and operational/publication approvals are separate required gates. No later gate is claimed by this statement approval.
