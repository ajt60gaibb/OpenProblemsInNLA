# MI-29 Lean formalization

The completed proof gives a negative answer to the full [canonical MI-29 conjecture](../README.md). Local compilation, kernel-trust checks, and two independent final AI-agent proof reviews passed. **The actual [Linux run 34706412510](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34706412510) accepted all five declarations at immutable [proof revision c0c5ece](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/c0c5eced77d2528f37d931200248fc54a190813e/matrix-inequalities-and-norms/MI-29/lean). The canonical status is Lean verified.** The [independent operational audit and original artifacts](verification/linux-2026-09-12/) record the exact source and dependency hashes, real sandbox controls, negative tests and default-kernel replay.

The mathematical counterexample is by **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Formalization: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. The new formalization code is licensed under [Apache 2.0](LICENSE); this does not reassign the informal proof's authorship. No external human peer review or source-author endorsement is claimed.

## Target and exact result

The original assertion quantifies every positive dimension, every complex positive definite matrix `A`, every invertible Hermitian matrix `B`, and every pair of real parameters `k,p ≥ 0`. It asks whether

```text
det(A^k + |AB|^p) ≥ det(A^k + |BA|^p).
```

The definitions use genuine unital `CFC.rpow` and `CFC.abs`, including the identity-matrix convention for exponent zero. A generic theorem proves that both determinants are positive real numbers, justifying the complex order used to express the inequality. No commutation or positivity of `B` is assumed.

The exact witness is `A = diag(2,1,1/2)` and `B = (1/5)·[[-1,2,0],[2,1,2],[0,2,1]]`, with `k=6,p=8`. The proof establishes positive definiteness of `A`, the Hermitian property and invertibility of `B`, and indefiniteness of `B`. It derives the actual functional-calculus identities `|AB|⁸ = (BA²B)⁴` and `|BA|⁸ = (AB²A)⁴`, then proves

```text
left determinant  = 136990346414301954149 / 61035156250000000000
right determinant = 4537743716162890657 / 1907348632812500000
right minus left  = 21036678407451 / 156250000000000 > 0.
```

This admissible strict counterexample refutes the complete original universal statement. The source's separate singular-input extension, established `k=2` result, and positive-`B` variants are outside this formalization.

The immutable informal sources are the [canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-29/README.md) and Colbrook's [complete manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-29/solution.tex) at revision `e7252e5`. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) preserves the reviewed statement-first plan. Its initial-stage wording is historical; the completed proof and final referee reports record the later outcome.

## Declarations and review boundary

| Export in `Solution.lean` | Certified content |
| --- | --- |
| `NLA.MI29.spectralPower_natCast` | Actual spectral powers agree with matrix natural powers, including zero. |
| `NLA.MI29.modulus_power_eight` | Genuine modulus square-root identity, positivity, and eighth-power reduction. |
| `NLA.MI29.comparison_positive_real` | Both determinants are positive real numbers under the full original hypotheses. |
| `NLA.MI29.counterexample` | Every witness hypothesis, CFC reduction, exact determinant, and strict violation. |
| `NLA.MI29.not_modulusDeterminantConjecture` | Negation of the complete canonical conjecture. |

[Definitions](NLA/MI29/Definitions.lean) and [Challenge](Challenge.lean) were frozen before implementation and approved by [statement referee 1](reviews/statement-referee-1.md) and [statement referee 2](reviews/statement-referee-2.md). The five deliberate Challenge placeholders specify the verification interface; `Solution` does not import Challenge and its proof dependency chain contains no placeholders.

[Final proof referee 1](reviews/proof-referee-1.md) and [final proof referee 2](reviews/proof-referee-2.md) independently inspected and re-elaborated the actual completed proof. Their [first](verification/referee-1/) and [second](verification/referee-2/) command, numerical reconstruction, and axiom records remain available. They applied relevant Tau Ceti correctness, fidelity, scope, quality, reuse, and attribution rubrics. These are independent AI-agent reviews, not an official Tau Ceti service verdict. Source-level identity checks are supplemented by the successfully audited isolated Linux Comparator run.

[Proof.lean](NLA/MI29/Proof.lean) uses generic Mathlib CFC lemmas, verified repeated-square matrices, and exact determinant expansion. Only one rational point comparison uses the minimal LeanCert point-inequality module in explicit kernel mode. That certificate is used by the strict counterexample and final negation. No interval subdivision, approximate matrix square root, numerical eigenvalue search, or native-execution trust is used. All five exports and the audited internal certificates depend only on `propext`, `Classical.choice`, and `Quot.sound`.

[comparator.json](comparator.json) selects exactly the five frozen Challenge exports, permits only those three standard axioms, and has no replaceable definition holes. [formalization.yaml](formalization.yaml) follows the pinned upstream v0.4 schema and records scope, source alignment, attribution, and the successful Linux gate.

## Reproduction

Toolchain and dependencies are pinned by [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json): Lean `v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

From this directory, with the pinned toolchain installed:

```
lake exe cache get
lake build Solution
```

For authoritative verification, use the repository's [Linux harness](../../../tools/lean/HARNESS.md) on a genuine Linux host after this unchanged project is committed. From the repository root:

```
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py \
  matrix-inequalities-and-norms/MI-29/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-29/lean \
  /absolute/path/to/nla-lean-tools
```

The harness separately builds the frozen Challenge and Solution, runs the real Comparator with default-kernel replay, and records source hashes and control results. The retained successful run executed remotely on GitHub Actions Ubuntu 24.04; its evidence was independently audited locally on macOS. All ten dependencies were freshly cloned at their pinned revisions. The official matching Mathlib cache was used, while the project's own mathematical modules were freshly elaborated. Mechanical formal identity and kernel acceptance supplement the independent English-to-Lean reviews.
