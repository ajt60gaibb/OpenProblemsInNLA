# FR-12 statements fixed before implementation

This is a statement package, not a completed formal verification. No `Proof.lean`
or `Solution.lean` exists at this stage. Two independent statement referees must
approve this exact package before proof implementation starts. The seven
placeholders in `Challenge.lean` intentionally prove nothing.

Mathematical proof and formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA, with substantial AI-agent assistance. Ferber, Jain and Zhao
retain credit for the original counting conjecture and published upper bound.
The source is the retained FR-12 README and George's `solution.md` at upstream
revision `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

## The complete original target

For each positive integer n, H(n) counts the individual real n by n matrices A
whose entries are either 1 or −1 and satisfy A Aᵀ = n I. Rows and columns retain
their labels. Signed permutations are not quotiented out. The conjecture asks
whether there is a positive real constant C such that

```math
H(n) \le 2^{C n\log_2 n}
```

for every positive multiple of four. `CountingConjecture` retains every one of
these quantifiers. Its logarithm is `Real.log n / Real.log 2`, its exponent is a
real exponent, and its count is `Nat.card` of exactly the displayed matrix
subtype. Finiteness of this subtype must be proved, not assumed. The definition
also extends the count to n = 0, but the original conjecture only quantifies
positive dimensions. There is no hidden choice of an equivalence-class count.

The full conjecture will be negated. The proof is permitted to refute a
universal assertion using the subsequence n = 2^(k+2); this does not narrow the
statement being refuted. No claim about Hadamard existence at every positive
multiple of four or a matching upper bound will be exported.

## Exact smaller construction

The source injection uses all perfect matchings of 2m row labels, giving the
factor (2m−1)!!. Its asymptotic argument then only uses the weaker bound m!.
We instead use exactly m! distinguishable matchings from the beginning.
For m ≥ 1, A,B genuine labeled order-m Hadamard matrices, and a permutation
σ of `Fin m`, construct

```math
C_{\rm top,i}=(A_i,B_i),\qquad
C_{\rm bottom,i}=(A_{\sigma(i)},-B_{\sigma(i)}).
```

`doublingMatrix` implements this formula with actual `Matrix.fromBlocks`, row
`submatrix`, negation, and `Matrix.reindex finSumFinEquiv finSumFinEquiv`.
The reindex identifies the first m labels and the last m labels in the
ordinary order; it does not identify or quotient any matrices.

The required mathematical obligations are:

1. Every output entry is a sign and its actual Gram product is (2m) I.
   Top/top and bottom/bottom products use the two original Gram identities;
   top/bottom products subtract the same Kronecker-delta contribution.
2. The top blocks recover A and B without ambiguity.
3. Distinct rows of A are distinct vectors. This follows from its Gram identity
   and m > 0: equal rows would have inner product both zero and m.
4. With A recovered, the bottom left block then recovers every σ(i). Therefore
   the actual map from the product of two matrix subtypes and a permutation is
   injective; this is a conclusion, never a premise.
5. Finiteness and the cardinality of `Equiv.Perm (Fin m)` give
   H(2m) ≥ m! H(m)^2. No unknown automorphism-group sizes enter the argument.

This is a restriction of the source's matching construction. The stronger
recurrence with (2m−1)!! is deliberately outside the formal exports. The exact
source lower bound and the full original conjecture remain in scope.

## Universal quantitative obligations

First prove H(2^k) ≥ 1 for every natural k, beginning with an actual order-one
matrix and iterating the proved construction. All logarithms of these counts
therefore have positive arguments.

For every even m = 2r with r ≥ 1, the elementary factorial estimate is

```math
(2r)! \ge r^r.
```

This can be deduced from Mathlib's exact factorial-product inequality, using
r! ≥ 1; no interval computation is needed. At m = 2^(K−1), K ≥ 2, the proved
recurrence implies, for a_K = log₂ H(2^K) / 2^K,

```math
a_K\ge a_{K-1}+\frac{K-2}{4},\qquad
a_K\ge\frac{(K-1)(K-2)}8.
```

The exported bound uses the harmless shift K = k+2, with every subtraction
eliminated from the natural-number expression:

```math
H(2^{k+2})\ge 2^{\,2^{k+2}k(k+1)/8}\quad(k\in\mathbb N).
```

Here 2^(k+2) inside the exponent is a natural power cast to the reals, while
the outer exponentiation is genuine real exponentiation. This is exactly
the manuscript's bound for every K ≥ 2, including k = 0 where the right side
is one. It is not an asymptotic notation in place of a quantified inequality.

Finally, for every positive real C, choose a natural k large enough that
k(k+1)/8 > C(k+2). Archimedean arguments must actually produce such a k in
Lean. Positivity of 2^(k+2), strict monotonicity of 2^x, and the actual logarithm
identity log₂(2^(k+2)) = k+2 give the strict counterexample to that C. The
selected dimension is positive and divisible by four. No bound on C, finite
list of dimensions, limiting approximation, or numerical sample is a premise.

## Seven frozen exports

| Challenge theorem | Required conclusion |
| --- | --- |
| `counting_semantics` | The exact matrix subtype is finite for every dimension; in positive dimension the sign/Gram definition is equivalent to actual Mathlib `Matrix.IsHadamard`. |
| `injective_doubling` | Every actual construction output is Hadamard, and the actual product-to-matrix map is injective, for every m ≥ 1. |
| `factorial_doubling` | The cardinalities of the actual matrix subtypes satisfy m! H(m)^2 ≤ H(2m). |
| `power_two_nonempty` | 1 ≤ H(2^k) for every natural k. |
| `power_two_lower_bound` | The precise displayed bound for every natural k. |
| `counterexample` | Every positive real C fails strictly at some dimension 2^(k+2). |
| `not_countingConjecture` | Unconditional negation of the complete original conjecture. |

`counting_semantics` must bridge real signs to Mathlib's unitary-entry predicate
and derive the other Gram identity in positive dimension. It cannot replace
the count with a count of an assumed family. All output signatures are in
namespace `NLA.FR12`. Comparator will compare them to the independently
approved Challenge, with an empty definition-name exception list.

## Computation and trust policy

This is an exact universal construction, counting and real-analysis proof.
Use symbolic block identities, finite-type cardinality theorems, factorial
bounds and exact power/logarithm identities. Do not enumerate large matrix
sets, perfect matchings, automorphism groups, or a growing grid of exponents.
Retaining full pair/matrix labels while restricting the constructed family
removes expensive combinatorial bookkeeping without weakening the target.

LeanCert is pinned and will supply explicit `#assert_trust kernel` checks for
the completed results. There is no analytical need for an interval certificate;
do not add a decorative numerical inequality to simulate one. If an actual
interval obligation emerges, minimize it, record its exact target, and use
kernel-checked certificates rather than native evaluation. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted final theorem axioms.

The statement package's small Python reconstruction checks m = 1 and m = 2
using exact integers. It checks 4 and 128 distinct outputs respectively under
the restricted construction (with H(1) = 2 and H(2) = 8 as input counts).
Those are construction output counts, not claims that H(2) = 4 or H(4) = 128.
Such diagnostics neither prove injectivity for all m nor certify the final
asymptotic theorem. The universal obligations above require actual Lean proofs.

After both statement approvals, implement proofs, obtain two independent final
referee reports applying the relevant Tau Ceti standards, and run actual Linux
Comparator and default-kernel replay. macOS development builds alone do not
establish that the Linux checker or its isolation controls passed.
