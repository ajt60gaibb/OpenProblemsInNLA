# KE-03 Lean proof guide

This project formalizes the entire [KE-03 exact-query problem](../README.md).
Its exported theorem is `NLA.KE03.complete_query_algorithm`, with the statement
`∃ C : ℝ, 0 < C ∧ SolvesKE03 C`. The proof uses the explicit constant
`C = 32768`, giving the requested exponents `a = 1` and `b = 2`.

For every positive dimension, supplied `K ≥ 1`, `0 < ε < 1/2`, and complex
diagonalizable matrix with Euclidean diagonalizer condition number at most
`K` and positive spectral radius, the concrete algorithm terminates on every
seed. It makes at most
`32768 * (1 + log(n*K)) / ε^2` exact matrix-vector queries on every seed.
With uniform-seed probability at least `99/100`, its output `z` and one actual
eigenvalue `μ` satisfy both
`(1-ε) * radius(A) ≤ ‖μ‖` and `‖z-μ‖ ≤ ε * radius(A)`.
Repeated eigenvalues, tied comparisons, and arbitrary spectral scales are included.

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records the frozen statement,
source revision and hashes, constants, domains, and computational model.
[Definitions.lean](NLA/KE03/Definitions.lean) contains the actual algorithm
and target definitions. `Eigenvalue` requires a nonzero eigenvector;
`radius` is the supremum of the norms of these eigenvalues. Matrix norms
are explicitly induced by `Matrix.toEuclideanCLM` on `EuclideanSpace`.
Unbundled diagonal lists and inverse-diagonalizer rows use the ordinary
function supremum norm as intermediate quantities; the queried vectors and
`opNorm` retain the Euclidean norms specified by the problem.

## Algorithm and proof

1. Draw integer coordinates independently from `Fin N`, where
   `N = 2^(Nat.log 2 (1024*n) + 1)`. The formal probability law is the exact
   cardinality ratio on `Fin n → Fin N`. As `N` is a power of two, this law
   admits sampling with `n * (Nat.log 2 (1024*n) + 1)` independent fair bits.
2. Put `η = ε^2/1024`, `F = 2*n*N*K`. Search sequentially for the first
   positive integer `m` satisfying `F ≤ (1+η)^m`. Store the transcript
   `[A^m b, ..., A b, b]`, using exactly `m` charged oracle transitions.
3. If `A^m b = 0`, return zero. Otherwise enumerate positive rationals
   until finding `r` with
   `r^(2*m) ≤ ‖A^m b‖^2 ≤ ((1+η)*r)^(2*m)`.
4. Construct a finite rational stereographic mesh of the unit circle.
   Reconstruct every shifted power `(A+sI)^m b` from the stored vectors
   by the binomial formula. Select a mesh direction maximizing its squared
   shifted-power norm, and return `r` times that direction.

The finite-counting argument differs slightly from the informal source's
normalized grid. In each row of the inverse diagonalizer, choose a coefficient
of maximal modulus. With all other integer coordinates fixed, at most one
coordinate choice makes the row action smaller than half that modulus.
The union bound over rows gives failure probability at most `n/N < 1/1024`.

On the resulting single good-seed event, two-sided norm estimates hold for
**every shift and power**, with distortion `F`. This uniformity allows all
later shifts to depend on the same transcript. The rational radius search,
mesh coverage, and shift maximization then locate one eigenvalue satisfying
both output inequalities. The geometric estimate actually proves distance
at most `ε * radius(A) / 2`. Logarithmic estimates for the degree supply the
explicit worst-case query constant.

| Module | Role |
| --- | --- |
| `Definitions` | Frozen oracle algorithm, finite seed law, eigenvalues, radius, and complete target |
| `Search` | Termination and specifications of the searches, squared norms, and query traces |
| `Probability` | Grid size and simultaneous row anti-concentration by finite counting |
| `MatrixBounds` | Actual spectrum of a diagonalization, spectral radius, and shifted-power norm bounds |
| `Degree` | Universal `32768 * (1+log(n*K))/ε^2` query bound |
| `History` | Transcript indexing and exact binomial reconstruction of shifted powers |
| `CircleNet` | Unit norms and quantitative coverage of the rational circle mesh |
| `Selection` | Finite comparison fold and selected maximizer |
| `PowerEstimates` | Radius and shifted-radius estimates from power comparisons |
| `Geometry` | Near-extremal eigenvalue location from the selected shift |
| `Correctness`, `Solution` | All-seed termination, query accounting, success probability, and exported theorem |

## Exact arithmetic and verification

The computation model permits exact real arithmetic and comparisons. Each
`searchNat` denotes sequential trials, with a `Part` domain recording
termination; the proof establishes that domain for every seed, including
failure seeds. Trial predicates use finite arithmetic expressions and
comparisons. Squared norms use sums of real and imaginary coordinate squares.
Eigenvalues, diagonalizers, real roots, and real logarithms occur in the analysis and
specification, rather than as extra oracle inputs or algorithmic primitives.
Only the transcript builder receives the matrix-vector oracle. No adjoint
or shifted-solve oracle is used.

The guarantee bounds matrix-vector queries. It does not bound scalar work,
search lengths, total runtime, memory, bit complexity, or floating-point
error. The Lean definitions describe the exact-real algorithm; they are not
presented as a finite-precision executable implementation.

The project pins Lean `4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`; transitive dependencies are pinned in
[lake-manifest.json](lake-manifest.json). From the repository root:

```sh
cd eigenvalues-and-inverse-problems/KE-03/lean
lake exe cache get
lake build
```

For the separate authoritative check, run the repository's pinned harness
from the repository root in its supported unprivileged Linux sandbox:

```sh
tools/lean/bootstrap.sh /tmp/nla-ke03-checker
tools/lean/verify.sh eigenvalues-and-inverse-problems/KE-03/lean /tmp/nla-ke03-checker
```

[Challenge.lean](Challenge.lean) is the independent comparison statement;
its deliberate placeholder is excluded from the solution import graph.
[comparator.json](comparator.json) permits only `propext`, `Classical.choice`,
and `Quot.sound`, with no replaceable definitions. The proof uses exact
algebra and inequalities; no numerical interval certificate or trusted native
evaluation is needed. Consult [verification/](verification/) and
[reviews/](reviews/) for the actual recorded checks, their scope, and reviewed
source hashes. A local macOS build is distinct from the Linux Comparator run.

The mathematical resolution is credited to Matthew J. Colbrook, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge,
as recorded in the [informal solution](../solution.md). The Lean implementation
was developed by OpenAI Codex agents. Authorship, automation, and independent
AI-agent review are reported separately; this guide is coauthored proof
documentation, not an independent referee report or a claim of human endorsement.
