# MI-21 Lean formalization

The complete proof refutes the full [canonical MI-21 conjecture](../README.md). Local compilation, standard-axiom checks, **two independent statement reviews and two independent final proof reviews passed**. **Linux Comparator verification is pending; the canonical status remains Solved.**

Mathematical counterexample and informal proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. New formalization code is under [Apache 2.0](LICENSE). No external human peer review or source-author endorsement is claimed.

## Complete target and witness

The original assertion quantifies all positive numbers of summands and dimensions, all positive definite complex input families, every real `t ∈ [0,1]`, `s,r,p > 0` with `sr ≥ 1`, and **every unitarily invariant complex matrix norm**. Its powers are genuine spectral powers, and its weighted mean is

```
X #t Y = X^(1/2) (X^(-1/2) Y X^(-1/2))^t X^(1/2).
```

With `A=∑ Ai` and `B=∑ Bi`, it asks whether

```
ν(∑ (Ai^s #t Bi^s)^r)
  ≤ ν((A^((1-t)srp/2) B^(tsrp) A^((1-t)srp/2))^(1/p)).
```

The definitions preserve the original noncommuting factor order, use actual `CFC.rpow`, and spell out the full complex norm axioms and independent left/right unitary invariance. The selected `operatorNorm` is the norm of `Matrix.toEuclideanCLM` on actual complex Euclidean space, and its membership in the full permitted norm class is proved.

The rational witness uses two summands of order two:

```
C = diag(12/37, 21/29),  E = diag(35/37, 20/29),
S = [[15,8],[8,-15]] / 17,
A1 = C², A2 = E², B1 = S E² S, B2 = S C² S.
```

All four matrices are proved positive definite, and both aggregate sums are the identity. At `s=t=1/2` and `r=2`, the actual right expression equals the identity for every `p>0`. The actual left expression is

```
L = [[8216600,-985600],[-985600,11912600]] / 12158163.
```

The nonzero complex vector `(1,-4)` is an eigenvector with eigenvalue `1351000/1350907 = 1 + 93/1350907 > 1`. The proof derives this as a lower bound on the genuine operator norm of `L`, while the right norm is exactly one. This strictly reverses the proposed inequality for every positive `p`; choosing `p=1` refutes the complete universal conjecture. No norm, parameter, positivity or commutation restriction is added to that target.

## Analytic proof and computation

The [proof](NLA/MI21/Proof.lean) first proves a generic CFC geometric-mean identification from a positive Riccati solution. It derives both inverse-half-power identities, identifies the genuine positive square root by uniqueness, and preserves every matrix multiplication order. A scaled version introduces a positive scalar square root whose square cancels analytically. Both actual means have independent exact inverse and rational Riccati certificates, so no mean identity is assumed.

A generic Euclidean eigenvector argument supplies the genuine operator-norm lower bound. Only the rational point inequality `1 < 1351000/1350907` uses the minimal LeanCert point-inequality module in explicit kernel mode. Its [printed certificate and consumers](verification/proof-inspection.log) show that it participates in the norm bound, strict counterexample and final negation. There is no interval subdivision, numerical matrix-square-root approximation, eigenvalue search or native-execution trust.

The immutable [canonical source](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-21/README.md) and [complete Colbrook manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-21/solution.tex) are cited at reviewed revision `e7252e5`. [SOURCE_MAPPING.md](SOURCE_MAPPING.md) and [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) retain the statement-first source mapping and obligations. Their stage-one wording is historical; completed proof and review status are recorded here and in the final reports.

## Three exports and independent reviews

| Export in `Solution.lean` | Proved content |
| --- | --- |
| `NLA.MI21.operatorNorm_isUnitaryInvariant` | Generic admissibility of the genuine Euclidean operator norm. |
| `NLA.MI21.counterexample` | All witness hypotheses, actual CFC identities and strict norm violation for every `p>0`. |
| `NLA.MI21.not_geometricMeanNormConjecture` | Negation of the full original matrix, parameter and norm assertion. |

[Statement referee 1](reviews/statement-referee-1.md) and [statement referee 2](reviews/statement-referee-2.md) approved the frozen [Definitions](NLA/MI21/Definitions.lean) and [Challenge](Challenge.lean) before implementation. [Final proof referee 1](reviews/proof-referee-1.md) and [final proof referee 2](reviews/proof-referee-2.md) independently read and freshly re-elaborated the actual complete proof. Their [first](reviews/proof-referee-1-root-evidence/) and [second](reviews/proof-referee-2-evidence/) evidence sets contain actual commands, logs, proof-term inspections, pin checks, and independent rational reconstructions.

The proof implementer does not count as an independent referee. Relevant Tau Ceti correctness, fidelity, scope, quality, reuse and attribution rubrics were applied within MI-21's scope; this is not an official Tau Ceti service verdict.

The local [3147-job build](verification/proof-build.log) and both independent final re-elaborations passed. Every one of the eight audited internal declarations and three public exports uses only `propext`, `Classical.choice`, and `Quot.sound`; see the [axiom record](verification/proof-axioms.json). The proof chain contains no theorem holes and never imports Challenge. Its three deliberate placeholders specify the independent statement boundary and are excluded from proof sorry counts.

[comparator.json](comparator.json) selects exactly those three frozen Challenge exports, has no replaceable definition holes, and permits only the standard three axioms. [formalization.yaml](formalization.yaml) uses the pinned real v0.4 schema. [Frozen input hashes](verification/proof-freeze.json) and [source-level identity checks](verification/proof-statement-identity.json) support review; actual Linux Comparator verification remains required.

## Reproduction

The [toolchain](lean-toolchain), [package configuration](lakefile.toml), and [dependency manifest](lake-manifest.json) pin Lean `v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

From this directory, with the pinned toolchain installed:

```
lake exe cache get
lake build Solution
```

For authoritative verification, run the repository's [Linux harness](../../../tools/lean/HARNESS.md) on genuine Linux after the unchanged project is committed. From the repository root:

```
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py \
  matrix-inequalities-and-norms/MI-21/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-21/lean \
  /absolute/path/to/nla-lean-tools
```

The harness separately compiles Challenge and Solution, uses real Comparator with default-kernel replay, and records hashes and sandbox/control outcomes. The local macOS builds reused pinned dependency artifacts and do not stand in for that remote verification. A successful Linux run and independent operational audit must be recorded before a Lean-verified catalog promotion.
