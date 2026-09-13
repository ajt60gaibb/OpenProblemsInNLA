# MF-16: a formal counterexample to order-two word uniqueness

**The complete nine-export proof passed independent mathematical review and actual Ubuntu Comparator/default-kernel verification.** The [canonical problem](../README.md) records the full target as **Lean verified**. The immutable checked revision and retained evidence are documented below.

Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains authorship of the mathematical counterexample. Hillar–Johnson and Armstrong–Hillar retain the original question's attribution. The new formalization has an Apache 2.0 license; it does not relicense the source manuscript.

## Complete target and actual counterexample

[Definitions](NLA/MF16/Definitions.lean) retains every finite ordinary two-letter palindrome containing `X`, every complex Hermitian positive definite pair `B,P` of order two, and the assertion that exactly one complex Hermitian positive definite `X` satisfies the word equation. Products use the actual written-order `List.prod` and genuine matrix multiplication. No real-only restriction or additional premise is added to the universal conjecture being refuted.

The unchanged source word is `X B X^12 B X`, with 16 letters, 14 occurrences of `X` and two of `B`. The unchanged matrices are

```
B  = [[1, 4], [4, 17]],
X0 = [[3, 0], [0, 1]],
P  = [[4783113, 6377496], [6377496, 8503345]].
```

The proof establishes their genuine positive definiteness after complexification and the actual equality at `X0`. It then proves the existence of another real symmetric positive definite solution whose first diagonal entry exceeds three. Its complexification is a distinct complex Hermitian positive definite solution, contradicting the complete original universal uniqueness claim.

[Solution](Solution.lean) has exactly the nine frozen [Challenge](Challenge.lean) signatures:

| Export | Proved contract |
| --- | --- |
| `word_semantics` | The actual word is an ordinary palindrome with the stated counts and written-order real and complex matrix-power formulas. |
| `source_data` | The unchanged complex matrices are positive definite, the word at `X0` equals `P`, and the exact determinants are proved. |
| `twelfth_power_reduction` | Every real symmetric order-two matrix of determinant three satisfies the explicit trace-polynomial twelfth-power identity. |
| `polynomial_word_equivalence` | For every real triple, the actual polynomial Expr system is zero exactly when determinant three and the two actual matrix-entry equations hold. |
| `krawczyk_certificate` | The complete actual LeanCert checker accepts, with exact preconditioner determinant, box radius and whole-box contraction bound below `27/1000`. |
| `certified_root` | There exists exactly one actual real system zero inside the specified box. |
| `root_to_matrix` | Every such root yields a genuine complex positive definite matrix, the full matrix word equality and a solution different from `X0`. |
| `counterexample` | The actual admissible word and complex positive definite `B,P` have at least two distinct positive definite solutions. |
| `not_wordUniquenessConjecture` | Unconditional negation of the complete original universal uniqueness assertion. |

The source also certifies three solutions and gives a threshold for an exponent family. Those stronger assertions are outside these exports. Two solutions suffice to refute the full original uniqueness target.

## Minimized exact certificate and genuine matrix bridges

The [numerical targets](NUMERICAL_TARGETS.md) and [source correspondence](SourceCorrespondence.md) were written and independently reviewed before implementation. A single three-dimensional rational box has radius `1/10000000`; its center and preconditioner use modest rational precision. The determinant-three equation keeps all three coordinates independent and avoids inverse-expression automatic differentiation.

[CayleyHamilton](NLA/MF16/CayleyHamilton.lean) applies the actual matrix characteristic-polynomial theorem. A scalar polynomial remainder reduces the twelfth matrix power before interval evaluation. The actual Expr equations are then proved equivalent in both directions to determinant three and the first two entries of the actual word. Matrix symmetry, determinant multiplicativity and the nonzero first target entry recover the remaining entry. An invertible LDL congruence proves genuine complex positive definiteness; ring-homomorphism identities transport all products and powers to complex matrices.

[Numerical](NLA/MF16/Numerical.lean) proves the complete `krawczykCheck` Boolean by `decide +kernel` and applies `LeanCert.Engine.krawczykCheck_sound`. The retained Boolean helper is `NLA.MF16.actual_krawczyk_checked._proof_1_1`. Its actual root theorem feeds full matrix recovery, distinctness and the final universal negation. Box-local uniqueness of the polynomial zero is distinct from the global matrix-word uniqueness that is disproved.

No root approximation is assumed. No degree theorem, native execution trust, numerical eigenvalue calculation, interval subdivision or unproved power-reduction identity is used. [PROOF_MAP.md](verification/PROOF_MAP.md) records the actual dependency chain.

## Review and checks actually performed

Two independent statement approvals preceded the first proof edit. The [proof freeze](verification/proof-freeze.json) binds 182 project inputs and 14 original Git source files; the 181 other proof inputs and 44 other statement inputs remain unchanged. The exact prior statement-stage README is retained in [the historical archive](verification/pre-candidate-README.md).

The main implementation agent was `/root/leancert_examples`, the Cayley–Hamilton helper author was `/root/solved_statement_inventory`, and `/root` made a disclosed computation-route contribution. These agents are not independent final mathematical referees. The independent [first final report](reviews/final-referee-1.md) and [second final report](reviews/proof-referee-2.md) both approve the exact complete frozen mathematics. [Coordinator acceptance](verification/final-review-acceptance.json) binds both reports and their complete evidence inventories. Each referee ran ten successful fresh source checks, obtained 26 standard-three axiom reports, inspected the material full-negation proof path and independently reconstructed the exact interval and matrix polynomial data. No human peer review, official Tau Ceti endorsement, source-author endorsement or new mathematical priority is claimed.

The final author validation ran ten successful fresh direct-source commands on macOS. It checked all implementation modules, Solution, an actual-term inspector, and separately Challenge. There were 26 kernel assertions and standard-three axiom reports. The inspector followed 110 reached project declarations and selected actual LeanCert soundness steps, including the material AD, fixed-point, characteristic-polynomial and complex matrix recovery dependencies. All proof modules passed without warnings. Only the nine separate intentional Challenge placeholders warned.

Every project object was initially absent from the author's fresh private prefix. The ten exact pinned MI-22 dependency sources and objects were reused read-only; no old MF-16 or MI-22 project object was imported. This is local source elaboration, not a Linux or Comparator result. Raw commands, source snapshots, failed development attempts and successful outputs are retained.

The solution does not import Challenge and has no admission or custom axiom. Kernel trust and [Comparator configuration](comparator.json) permit only `propext`, `Classical.choice` and `Quot.sound`. Every advertised export is selected and `definition_names` is empty. Comparator checks formal statement identity; the independent statement reviews check correspondence to the informal original target.

## Reproduction

Lean is pinned to 4.33.1, Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926`. [lake-manifest.json](lake-manifest.json) pins all ten dependencies. With the project's own exact dependencies installed, explicitly build the proof:

```
lake build Solution
```

The unchanged default Lake target is `Challenge`; plain `lake build` therefore checks the reference statements. Its placeholders are not proofs. Reproduce the authoritative check from the immutable revision using the repository's [Linux verification workflow](../../../.github/workflows/lean-verification.yml) and [pinned checker instructions](../../../docs/lean/README.md). It runs Comparator, actual default-kernel replay and both real rejection/control suites on non-root Ubuntu.

## Actual Ubuntu verification and publication preservation

[Run 34735259429](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34735259429) checked immutable candidate `4e24448897a088ca9e7458379add1014c5d11e0c`. All 17 jobs and every step passed. The actual checker ran on Ubuntu 24.04 x86_64 with UID 1001, Lean 4.33.1, the pinned Comparator/exporter and strict sandbox. It freshly cloned ten exact dependencies and used 8,690 matching official Mathlib cache files. Challenge and Solution build graphs had 2,840 and 2,863 jobs; these are not counts of a full dependency-source rebuild.

Both actual export lists contain exactly the nine advertised declarations, with no definition exceptions. Default-kernel replay accepted the Solution. All 22 actual source axiom reports match their explicit kernel assertions and contain only `propext`, `Classical.choice`, `Quot.sound`. The final referees' count of 26 additionally includes four computational helper checks; their original evidence is retained. The Solution phase has no warnings or admissions.

The target and standalone checker jobs each executed the actual sandbox probes, three raw-kernel controls, five Comparator fixtures and admission/native rejection controls. The deliberately admitted proof was rejected for `sorryAx`, and native computation for `checked._native.native_decide.ax_1_1`. Nested Bubblewrap was denied UID-map setup before its inner write; the logs do not establish an executed inner-write denial or general sandbox security.

The [independent operational review](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [complete outer inventory](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) bind 466 evidence files plus the inventory, including all seven nested candidate manifests. The retained 294-input source snapshot agrees with the actual verifier receipt and committed Git blobs. Original project artifact ZIP SHA256 is `0dad309f58da9d61b1b177a550f60d8053938409bc30fe9d57399b719aec1d34`; checker ZIP SHA256 is `62d95b1cd2d2d34e82f0fc95c38cb1a2c2f9257caa7c9af5b50ca95eccf44f66`. Both match GitHub metadata and actual upload logs. The complete 217-log run ZIP is retained with a separately computed digest, without claiming a GitHub-published checksum for that log archive.

Operational reviewer `/root/mf16_final_referee` also served as independent final mathematical referee 1 and independent candidate packaging reviewer. These roles add no mathematical approval. `/root` independently accepted that operational evidence and prepared these publication wrappers, but is a disclosed proof-route contributor and does not count as an independent final mathematical referee. Referee 2 remains `/root/formal_review_standards`. The [root acceptance](verification/root-operational-2026-09-12/ROOT-CHECKS.json) and its complete inventory bind six files plus that outer manifest.

The actual run checks the immutable candidate, not these later publication wrappers. Among its 294 inputs, publication changes only this README and five status/review fields in the [v0.4 manifest](formalization.yaml); the other 292 inputs remain unchanged. Both exact candidate wrappers are archived under [publication evidence](verification/publication-2026-09-12/archive/). All 467 Linux evidence files, seven root operational files, 182 frozen proof inputs through the historical README archive, 45 statement inputs and fourteen original source snapshots remain intact. The canonical original mathematical target and source manuscripts are unchanged. Earlier pending notices remain historical phase records.

The campaign's pinned Schiffer and Forsythe examples and adapted Tau Ceti protocol are credited in the source correspondence and metadata. Separate publication review is required before commit, fork push and individual upstream PR. No new proof run over these wrappers, external human review, official Tau Ceti endorsement or mathematical priority is claimed.
