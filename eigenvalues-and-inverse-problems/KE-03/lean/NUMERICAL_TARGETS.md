# KE-03: frozen full target and exact computational model

## Source and scope

Canonical source revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
The original problem is `eigenvalues-and-inverse-problems/KE-03/README.md`,
SHA256 `6e2f296520b00a62662c156f84cba6d69455f8caffbf57067ee888de3a5dfbc2`.
The complete informal proof is the adjacent `solution.md`, SHA256
`e8696c97fbb703463f2fc5b8f146a8ac06f058176ee7c979711ddd620e4e1b60`;
its `solution.tex` has SHA256
`123aeda0ac5bc2fb7eee61ab9a7b8baf658f5b624dcd61019afde00cddbf1a8e`.
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, receives mathematical-resolution credit. The original
problem and prior-result authors retain the credit in the canonical page.
The new implementation is authored by OpenAI Codex agents; no author or human
endorsement is asserted.

The target is the **entire original exact-query question**. There exists a
single uniform randomized algorithm and a universal real constant `C > 0`
such that, for every positive integer `n`, real `K ≥ 1`, real `0 < ε < 1/2`,
and complex `n × n` matrix `A` having a diagonalization with Euclidean
condition number at most `K` and positive spectral radius, the algorithm:

1. Terminates for every random seed.
2. Uses at most `C * (1 + log(n*K)) / ε^2` exact `v ↦ A v` queries on every seed.
3. With probability at least `99/100`, outputs a complex `z` for which one
   actual eigenvalue `μ` simultaneously satisfies
   `(1-ε) * radius(A) ≤ |μ|` and `|z-μ| ≤ ε * radius(A)`.

This supplies the requested universal exponents `a = 1`, `b = 2`. No claim
about total arithmetic work, bit complexity, or floating-point stability is
part of the original question or this formalization. All dimensions,
repeated eigenvalues, ties, arbitrary spectral scales, and `K = 1` are included.

## Mathematical definitions

`Vec n` is `EuclideanSpace ℂ (Fin n)`. `act A` is
`Matrix.toEuclideanCLM A`, and `opNorm A` is its induced Euclidean operator
norm. No default entrywise or row-sum matrix norm is substituted.

`Conditioned A K` means that there exist complex square matrices `V`, `W`
and a diagonal list `λ` with both `V*W = 1` and `W*V = 1`,
`A = V * diagonal λ * W`, and `opNorm V * opNorm W ≤ K`. Neither these
witnesses nor the entries of `A` are inputs to the algorithm.

`Eigenvalue A μ` is the existence of a nonzero vector `v` with
`act A v = μ • v`. `radius A` is the supremum of norms of these actual
eigenvalues. The proof must establish that, under the promise in positive
dimension, this set is nonempty and bounded and its supremum is the maximum
of the diagonal list's norms. Positivity of that actual radius is the stated
input assumption, not an assumption about an unrelated supplied estimate.

The advertised theorem is exactly
`∃ C : ℝ, 0 < C ∧ SolvesKE03 C`.
`SolvesKE03` expands to all the quantifiers and guarantees above, for the
concrete `runAlgorithm` in `Definitions.lean`. Comparator must select
`NLA.KE03.complete_query_algorithm`, compare separate `Challenge` and
`Solution` modules, permit only `propext`, `Classical.choice`, and
`Quot.sound`, and have no replaceable definition holes.

## Exact algorithm and randomness

The random grid size is `N = 2^(Nat.log 2 (1024*n) + 1)`. For `n > 0`, the
proof must show `1024*n < N ≤ 2048*n`. A seed is a function
`Fin n → Fin N`, uniformly sampled from all `N^n` possibilities. Since
`N` is a power of two, this is a fixed finite number of independent fair
random bits. The seed law depends only on `n`, never on `A` or its spectrum.
The vector `b` consists of the seed's integer coordinates, embedded in ℂ.

Set `η = ε^2 / 1024` and `F = 2*n*N*K`. The degree search tests natural
numbers `k = 0, 1, ...` until `F ≤ (1+η)^(k+1)`, and returns `m = k+1`.
The algorithm stores `[A^m b, ..., A b, b]` in exactly `m` query transitions.
`QueryTrace` records an initial list at cost zero and one charged `A v` call
for each extension. Only `history` receives the oracle; all later helpers
receive this finite stored list.

The squared norm is the finite sum of the real and imaginary coordinate
squares. If the squared norm `S` of `A^m b` is zero, output zero. Otherwise,
enumerate natural pairs by `Nat.unpair`, interpret each as the positive
rational `r = (a+1)/(b+1)`, and stop when
`r^(2*m) ≤ S ≤ ((1+η)*r)^(2*m)`. This is finite exhaustive arithmetic search;
there is no root primitive or semantic choice of a spectral radius.

Search for positive `q` with `32 ≤ ε*q`. The candidate circle list contains
`1` and both signs of
`u(t) = (1-t^2)/(1+t^2) + (2*t)/(1+t^2) * I`
for rational `t = -1 + 2*j/q`, `0 ≤ j ≤ q`. The proof must show that all
candidates have norm one and every unit complex number is within `ε/8`
of a candidate. Squared shifted-power norms are computed from the stored
history by the finite binomial expansion. A finite comparison fold selects
a maximizing candidate, keeping the earlier candidate on a tie. Return `r*u`.
These steps use neither `A*` nor shifted linear-system queries.

`searchNat` has type `Part ℕ`: its domain is that some finite trial succeeds,
and its result is the least successful trial (`Nat.find`). This is a
denotational specification of sequential search, not an algorithmic test of
an existential statement. Every predicate instantiated by the algorithm is
an explicit finite combination of arithmetic and comparisons. The full
theorem must prove the domain for every seed, including failure seeds.
Real comparison is a primitive of the permitted exact-real model. The Lean
definitions are not advertised as an executable finite-precision program.

## Proof route and deviations from the source

The source's normalized rational random grid is replaced by an integer grid.
For each row of the inverse diagonalizer, fix a largest-modulus coefficient.
For any assignment of the other seed coordinates, fewer than half that
coefficient's modulus can occur for at most one grid value. Union counting
over rows gives bad probability at most `n/N < 1/1024`; the required target
is only success probability `99/100`.

On the resulting simultaneous good-seed event, the proof must establish
two-sided norm estimates for **every** shift and power, using distortion `F`.
Consequently the estimates apply to shifts selected adaptively from the same
query history. Shift maximization and circle-net coverage then give the same
near-extremal eigenvalue for both output requirements. Logarithms, norms,
roots and diagonalizers may be used in this analysis; the concrete algorithm
uses only the arithmetic searches, squared norms, and comparisons above.

The logarithmic degree estimate must give one universal positive `C`.
The final proof may choose a generous value; sharp constants are not an
original requirement. No numerical experiment, approximate spectrum,
unproved certificate, restricted dimension, or favorable seed is a premise.
