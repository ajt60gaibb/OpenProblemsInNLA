# MI-07 Lean formalization

The completed proof gives a negative answer to the full original [MI-07 triangle conjecture](../README.md). Local Lean compilation, all 23 kernel-trust checks, and two independent final AI-agent proof reviews passed. **Authoritative Linux Comparator verification is pending. The canonical repository status remains Solved.** No Linux execution or Lean-verified catalog promotion is claimed by this package.

The mathematical counterexample is by **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. The formalization code is licensed under [Apache 2.0](LICENSE). Mathematical authorship is not reassigned, and no external human peer review or source-author endorsement is claimed.

## Original target and complete negative answer

For an arbitrary complex square matrix X, the canonical maximal symmetric modulus is

```text
|X| = (X* X)^(1/2)
M(X) = lim_(m → ∞) (|X|^m + |X*|^m)^(1/m),  m a positive integer.
```

The assertion quantifies every positive dimension and every pair of complex matrices A,B. It asks for complex unitaries U,V satisfying ordinary positive-semidefinite domination

```text
M(A+B) ≤ U M(A) U* + V M(B) V*.
```

The definitions retain these full quantifiers, actual `CFC.abs`, actual real `CFC.rpow`, and ordinary PSD order. The generic topology theorem identifies the finite-dimensional root limit with convergence in the genuine Euclidean operator norm. No positivity, self-adjointness, commutation or reality restriction is added to the arbitrary inputs or unitaries.

Colbrook's family is specialized to t=5/12:

```text
A = P = [[1,0],[0,0]],   B = [[0,5/12],[0,0]],   s = 13/12,
Q = [[144,60],[60,25]]/169,   R = P + Q.
```

Exact matrix algebra proves that P,Q are PSD projections, R is positive definite, and all six proposed polar factors are the actual CFC moduli. For every nonnegative index r, the actual positive-integer root sequences are

```text
A:   2^(1/(r+1)) P                → P
B:   (5/12) I                    → (5/12) I
A+B: (13/12) R^(1/(r+1))         → (13/12) I.
```

The singular projection case uses its genuine spectrum and strictly positive exponents to preserve its nullspace. Continuity at exponent zero is used only for the positive definite matrix R. Each invocation of the totalized `Filter.limUnder` is identified from its corresponding proved convergence; no arbitrary fallback value or assumed convergence enters the counterexample.

The actual left trace is 13/6. For every pair of complex unitaries, cyclic trace invariance makes the right trace 11/6. Their right-minus-left difference has trace -1/3, which excludes PSD domination for every U,V. This refutes the complete original constant-one conjecture. The informal manuscript's stronger theorem excluding every finite domination constant, and generic convergence for unrelated complex matrices, are outside these exports.

The immutable sources are the [canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-07/README.md) and Colbrook's [complete manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-07/solution.tex), Theorem 1.1 and its proof. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) preserves the independently approved statement-first plan. Its initial-stage wording is historical; the [completion record](reviews/proof-completion.md) and final referee reports record the later proof outcome.

## Seven exports and review boundary

| Export in `Solution.lean` | Certified content |
| --- | --- |
| `NLA.MI07.modulus_eq_sqrt` | Genuine positive square-root modulus and positivity for every complex matrix. |
| `NLA.MI07.maximalModulus_eq_of_tendsto` | Actual limit identification from a proved convergence. |
| `NLA.MI07.root_limit_iff_spectralNorm` | Root convergence is equivalent to convergence in the true spectral norm. |
| `NLA.MI07.witness_moduli` | All exact polar identities, projection identities, PSD and positive-definite facts. |
| `NLA.MI07.witness_root_limits` | The actual root sequences converge at all three invoked matrices. |
| `NLA.MI07.counterexample` | Actual maximal moduli and negative trace obstruction for every complex unitary pair. |
| `NLA.MI07.not_triangleConjecture` | Negation of the complete original universal constant-one conjecture. |

[Definitions](NLA/MI07/Definitions.lean), [Challenge](Challenge.lean), and the numerical plan were frozen before proof implementation. [Statement referee 1](reviews/statement-referee-1.md) and [statement referee 2](reviews/statement-referee-2.md) independently approved that boundary. Seven deliberate Challenge placeholders specify the formal comparison interface; `Solution` never imports Challenge, and its proof dependency chain contains no placeholders.

[Final proof referee 1](reviews/proof-referee-1.md) and [final proof referee 2](reviews/proof-referee-2.md) independently inspected every proof source and freshly re-elaborated Definitions, FunctionalCalculus, Proof and Solution. Their [first](verification/referee-1/) and [second](reviews/proof-referee-2-root-evidence/) raw commands, hashes, exact reconstructions, axiom audits and actual certificate inspections are retained. Relevant Tau Ceti correctness, fidelity, scope, proof-quality, reuse and attribution rubrics were applied within this canonical task. These are independent AI-agent reviews, not an official Tau Ceti service verdict. The proof implementer does not count as an independent referee.

[FunctionalCalculus.lean](NLA/MI07/FunctionalCalculus.lean) proves reusable projection-power, scalar-power and positive-definite continuity bridges using actual Mathlib CFC and spectral APIs. [Proof.lean](NLA/MI07/Proof.lean) connects them to exact 2x2 matrix identities, all three limits and the all-unitary contradiction. The sole LeanCert computation is the rational point check `0 < 1/3`, with explicit kernel trust. Its [actual checked certificate and consumer](reviews/proof-certificates.log) show that it is retained in the final negation. No interval subdivision, approximate matrix square root, numerical eigenvalue list or search over unitary matrices is used.

The local [3149-job build](reviews/proof-build.log) passed without warnings. All 23 internal/public kernel checks and [transitive axiom reports](reviews/proof-axioms.log) contain only `propext`, `Classical.choice`, and `Quot.sound`. No custom or native-execution axiom is permitted. Local macOS builds and source-level signature checks support, but do not replace, the pending actual Linux Comparator and default-kernel replay. Formal identity and kernel acceptance do not themselves replace the separate prose-to-Lean statement reviews.

[comparator.json](comparator.json) selects exactly the seven frozen exports, allows only those three standard axioms, and contains no replaceable definition holes. [formalization.yaml](formalization.yaml) follows the pinned upstream v0.4 schema and records scope, alignment, attribution and the pending Linux gate.

## Reproduction

[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json) pin Lean `v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and all ten dependency revisions. Local development and both independent referees used matching dependency artifacts while freshly elaborating this project's mathematical modules; this is not a fresh Linux dependency rebuild.

From this directory, with the pinned toolchain installed:

```sh
lake exe cache get
lake build Solution
```

After the unchanged project is committed, run authoritative verification on an isolated non-root Linux host satisfying the [shared harness prerequisites](../../../tools/lean/HARNESS.md). From the repository root:

```sh
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py \
  matrix-inequalities-and-norms/MI-07/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-07/lean \
  /absolute/path/to/nla-lean-tools
```

The harness separately builds and exports the frozen Challenge and actual Solution, performs actual sandbox and negative controls, compares all seven declarations, and replays the solution through Lean's default kernel. Its source lock and notices retain checker provenance, including the Forsythe workflow reference. A successful real Linux execution and independent operational audit are still required before any canonical promotion to Lean verified.
