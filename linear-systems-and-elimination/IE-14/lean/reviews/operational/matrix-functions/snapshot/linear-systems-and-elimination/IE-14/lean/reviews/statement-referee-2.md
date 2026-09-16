# IE-14 — independent exact pre-proof statement referee 2

**Verdict: APPROVE the ten submitted boundary inputs, with no requested mathematical change.** They faithfully state the entire original IE-14 target and sufficient explicit semantic/witness obligations. This approves statements and the exact proof/certificate plan, not their unimplemented proofs. Canonical status remains **Solved**; no LeanCert certificate, final theorem, Comparator or Linux verification is claimed by this review.

**Reviewer:** OpenAI Codex AI agent `/root/existing_verification_audit`, 15 September 2026. I have not implemented or edited an IE-14 definition, proof, statement, or dossier. I independently read the full canonical statement, complete retained manuscript and historical review, every proposed definition/export, the completed dossier, all ten input files and the proposed diagnostics. I apply the repository's [Tau Ceti review adaptation](../../../../docs/lean/REVIEW.md), without asserting human review or official endorsement.

## Exact identity and independent checks

[Submission manifest](statement-submission.json) SHA-256: **`9adea8e22570a4da8c3b8363697e66651ebd015ab7828d18b50c74f7ee6598e6`**. Published input base: **`d8c38a795876b132c90df8d1be8682d3dcde394c`**. The following actual file hashes were independently recomputed:

| Reviewed input | SHA-256 |
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

[Independent evidence receipt](statement-referee-2-evidence/review-evidence.json) SHA-256: **`fde143a03d8679c2a1d6fc5a1f2b5a259502c95dedd82e735a4228cfc2fa702d`**. It records the ten hashes, all seven original source hashes, actual dependency revisions and successful checks. Every original source file, including both PDFs and canonical TeX, matches its declared byte count/hash and the corresponding Git blob at the published base. The registry still maps IE-14 to its permanent canonical path. The full packaged manuscript hash is `4c20c2c20e6d05945911883682bc823096ef0ff1011cbd31bf941fd1f309b869`; the older recovered-source hash quoted in its preamble is correctly distinguished in the dossier.

My fresh snapshot at `/private/tmp/nla-campaign-existing-review/IE14-statement-build` used its own project build directory and only reused the pinned dependency packages. `lake build Challenge` passed **3008 jobs**, with exactly the **seven expected specification-only sorry warnings**. The snapshot source/configuration bytes remain identical to the submitted boundary. [Fresh build](statement-referee-2-evidence/fresh-challenge-build.log). I separately printed all seven actual elaborated types, expected placeholder axioms and the literal core definitions. [Audit source](statement-referee-2-evidence/BoundaryAudit.lean) and [output](statement-referee-2-evidence/boundary-types-and-definitions.log). These holes prove no mathematics.

I checked the actual Lean 4.33.1 binary and all ten package Git revisions against the manifest, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The supplied API-only probe also independently typechecked. The NLA tree contains only Definitions and Solution imports only Definitions, so this remains a genuine pre-proof submission.

## Full original target and seven exports — APPROVE

`Mat n` is genuinely complex. Every upper-bound quantifier includes all nonsingular cyclic inputs, every legal maximal-modulus **tie** choice, every active stage and every active entry. There are no reality, genericity, symmetry, diagonal dominance or deterministic-tie assumptions. The pattern allows zeros anywhere in the three bands and enforces both cyclic corner entries nonzero. For n≥4 the corner quantifier selects exactly `(0,n−1)` and its reverse.

`rowSwap` changes rows only, `trajectory ... 0` is the actual input, and `schurStep` is the literal Schur update with both discarded rows and columns padded by zero. `AdmissiblePivot` enforces an active selected row, nonzero divisor and largest complex modulus in the active pivot column. Thus total Lean division creates no extra admissible paths. No preliminary row or column permutation is allowed by the definition.

Finite `nnnorm` suprema define the actual entrywise maximum, not an operator norm. The semantic export proves attainment when n≥1. Growth includes precisely the n active stages from the unmodified input through the last scalar; the subsequent empty padded matrix does not contribute. The generic `admissible_path_exists` is stronger than the cyclic target and avoids vacuous all-path reasoning. Its n=0 case is consistent: the determinant is one and the unique empty path has no pivot obligations; no entry-maximum attainment is asserted there.

All seven exports match the dossier and Comparator:

1. `numerical_bounds`: the two exact real half-coefficient inequalities.
2. `entryMax_semantics`: nonnegativity, all-entry domination and actual maximizing indices.
3. `admissible_path_exists`: complete complex GEPP paths for every nonsingular input.
4. `all_active_entries_bound`: the full all-complex, all-tie, all-entry, all-stage inequality for every n≥4.
5. `witness_data`: the literal all-size matrix is nonsingular, has the required pattern/corners, and initial maximum one.
6. `witness_attainment`: the literal physical-row path is legal and has exactly the complete growth value.
7. `canonical_result`: an actual `IsGreatest` member of the complete growth set together with its `sSup` value, for every n≥4.

The greatest-element assertion includes nonemptiness and boundedness; an empty/unbounded real-supremum convention cannot discharge it. Attainment is stronger than the original request for approaching examples, as justified by the retained source. No finite diagnostic or final-pivot-only result replaces the full canonical target. Comparator names are exactly these seven, with no replaceable definition holes and only `propext`, `Classical.choice`, `Quot.sound` permitted.

## Analytic and indexing correspondence — APPROVE

I independently checked the dossier's original-label/front invariant against the entire source. The special original last row starts in the front; later rows remain unchanged until their first potentially nonzero pivot column. A legal nonzero pivot must lie among two old rows and the fresh row. This invariant must be proved from the literal trajectory; it is not hidden in an input definition. The dossier correctly warns that the **padded whole matrix** becomes singular after a step. Supported-vector active-block injectivity is a sound path-existence approach.

For an arbitrary complex multiplier of modulus at most one, the Schur entry bound uses the triangle inequality. The proposed maximum/sum formulation follows for **each** removed row: `M'≤max(T,M+c)` and `T'≤T+c+max(M,c)`. With a zero fresh target entry this yields `M'≤T` and `T'≤T+M`. It does not assume GEPP chooses its row using the target column. The source's zero target entry in a pivot row is not a zero pivot divisor.

The column histories exhaust the input, columns 1 and 2, ordinary middle columns, column n−1 and column n. The counts of zero-fresh updates, final two-row step and disappearing active target columns are consistent in both indexing conventions. In particular n=4 has one zero-fresh last-column update, zero such updates for column n−1, and an empty middle-column range. Fibonacci arguments never require a negative natural index. Carrying `entryMax A` multiplicatively is equivalent to normalization and avoids an unnecessary scaling theorem without changing any target.

The current `factorIndex` is the inverse of the source assignment `(1,n,2,...,n−1)`. It defines the input from `L*U`; it does not perform a forbidden preliminary permutation. The actual path keeps row 0 first, then selects the current last physical row at every later stage. Successive swaps indeed yield original labels `(1,n,2,...,n−1)`. The dossier's active factor-label formula and tail-product invariant are algebraically consistent with that **physical** path, including the final stage. It is not enough merely to assume an LU pivot order; that bridge remains an explicit implementation obligation.

The four witness-column cases give the full cyclic pattern, both corners ±1 and maximum one. The half entries in column 2, including their cancellation in factor row 2, are essential to the smallest-order pattern. The upper diagonal is nonzero in every n≥4, and the final scalar is `F_(n+1)+1`. Triangular determinant nonvanishing plus an actual row permutation suffices; the optional parity/determinant sign formula need not become a public theorem. The n=4 matrix, physical path, pivots and determinant recorded in the dossier match my independent arithmetic.

Primary alignment was independently checked during the immediately preceding reconnaissance in [Higham, Problem 9.15(b), printed p.193](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf). The explicit canonical complex-field, original-order and all-tie conventions are preserved, regardless of the source book's abbreviated wording.

## Independent arithmetic and certificate plan

My independently written [exact checker](statement-referee-2-evidence/independent-exact.py) uses only Fraction/Gaussian-rational arithmetic. It checks the literal definition branches and **current-position** path for every n=4,...,30: full forbidden-entry pattern, both corners, initial maximum, every chosen pivot and multiplier, complete active growth, and the determinant reconstructed from actual pivots. All **27** cases pass. It separately checks **138,240** finite complex front-update cases, including each possible removed row and complex multipliers with modulus at most one. The sum comparisons avoid floating-point square roots. [Results](statement-referee-2-evidence/independent-exact.json).

I also read and independently reran the submitted diagnostic. Its separate first-nonzero determinant routine, full factor-residual identity at each stage and recorded pivot rows give useful additional transcription checks. Both its result JSON and seven-source hash JSON reproduced **byte-for-byte**. These finite computations do not prove any all-size or all-complex theorem; all universal front, support, path and recurrence identities still require Lean proofs.

The proposed LeanCert calculation is deliberately small: prove `0 < (1/2:ℝ)` and `(1/2:ℝ)≤1` with explicit **kernel** trust. The strict bound must feed the actual half-pivot nonvanishing proof; the upper bound must feed the actual half-entry input bound, via correct real-to-complex norm identities. The final witness dependency must visibly contain that certificate. This is genuine numerical use and does not justify replacing symbolic Fibonacci/front proofs with enumeration. I approve this exact obligation and consumption plan; no certificate has yet been executed or accepted here.

## Reuse, documentation, attribution and gate

The dossier identifies usable pinned Mathlib finite-max, complex norm, Fibonacci, triangular determinant and supremum APIs, and accurately distinguishes reusable real IE-05/IE-15 patterns from the new complex partial-pivoting proof. In particular the rook/column-swap assumptions of IE-15 are not silently imported. The source `det_permute` signature, rather than a misleading docstring, controls any reindexing proof. The new original-label/front and witness physical-row invariants are explicitly outstanding work, not purported existing library results.

Matthew J. Colbrook retains the original proof credit and Cambridge affiliation. George Stepaniants has the requested Department of Computing and Mathematical Sciences, California Institute of Technology formalization affiliation, with AI assistance disclosed and no new contact email. Original statements, published IDs, manuscript and historical reviews remain unchanged. The dossier truthfully separates preparation diagnostics, agent reviews and future formal verification.

**Pre-proof gate: APPROVE these exact ten files.** The coordinator must combine both independent approvals and freeze the boundary before implementation. Later approval still requires the complete actual proof closure, independent final review, kernel LeanCert consumption, permitted-axiom checks, real pinned Comparator/default-kernel execution, sandbox/rejection controls and operational review. This report supports none of those unrun later claims. The retained evidence is sealed by [SHA256SUMS](statement-referee-2-evidence/SHA256SUMS).
