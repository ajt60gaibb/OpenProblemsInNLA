# RE-06 exact mathematical and numerical target

## Source and scope

`ORIGINAL.md` is a byte-for-byte copy of the complete canonical
`randomized-and-low-rank-approximation/RE-06/README.md` at published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. The affirmative source is
Sidney Holden's `randomized-and-low-rank-approximation/RE-06/solution.tex`,
Theorem 1.1 and Sections 2–6. This is a pre-implementation proposition
specification, not a proof or an independent review.

## Inputs, oracle, output, and objective

For **every** `n : ℕ` with `n ≥ 1`, an explicitly given finite family
`𝓕 ⊆ Matrix (Fin n) (Fin n) ℝ` has cardinal `M ≥ 2` and contains distinct
real `n × n` matrices. An ordered enumeration of the set may be supplied
to the algorithm for deterministic tie-breaking; it must not change the
finite set or its cardinal. The unknown `A` is an **arbitrary fixed** real
`n × n` matrix, with no norm, rank, gap, conditioning, or membership
promise. The accuracy parameter is **every** real `0 < ε < 1/2`.

The only access to `A` is a matrix–vector oracle. One query is a pair
`(side,v)` with `v : Fin n → ℝ` and `side ∈ {right,left}`; its answer is
exactly `A v` if right and `Aᵀ v` if left. The transpose is the ordinary
real transpose. **Each** query of either type counts one, including zero
or repeated vectors. The family and `ε` are ordinary explicit inputs;
matrix–vector multiplication involving a known candidate is free of
oracle cost.

Every execution returns a member `B ∈ 𝓕`. The objective uses the exact
Frobenius norm and a **finite attained minimum**

```text
OPT(A,𝓕) = min { ‖A-D‖_F : D ∈ 𝓕 }.
```

The event is the returned member's single inequality

```text
‖A-B‖_F ≤ (3+ε) · OPT(A,𝓕).
```

The guarantee is `Pr[event] ≥ 99/100` for **each fixed** admissible
`n,𝓕,A,ε`, with probability only over the algorithm's randomness. It is
not an average over inputs or candidate families. If `OPT=0` (equivalently
`A∈𝓕`), this event requires **exactly** `B=A`, not merely a small positive
error. Rank-deficient `A` or sketches remain within the input and execution
domain; no inverse, positive smallest singular value, or division by
`OPT` may be assumed in the public target.

## Fully nonadaptive randomized exact-real query model

There is **one uniform algorithm**, not a separate choice of code for
each matrix or dimension. Its complete query schedule is committed before
any oracle answer is read. A suitable Lean boundary may use a concrete
finite-program exact-real query machine, or a structurally two-phase
`plan`/`postprocess` machine with an operational program syntax:

1. `plan` receives `n`, the explicit family, `ε`, and random draws, but
   **no** `A`, oracle result, or function of a previous result. It halts
   with a finite ordered list of pairs `(side,v)`. Both all query vectors
   **and all choices of `A` versus `Aᵀ`** are fixed here. The plan may
   depend on `𝓕,ε` and randomness; the manuscript happens to use vectors
   distributed using only `n,M,ε`.
2. The oracle answers the entire committed list. `postprocess` receives
   only the explicit inputs, randomness, plan and stored answers; it may
   compute, compare, use exact SVD/pseudoinverse, and select a member of
   `𝓕`, but has **no oracle-call instruction**. Conditional reasoning
   about independent prequeried sketch blocks does not permit selecting
   another query after seeing any answer.
3. The exact-real model allows exact arithmetic, comparisons, standard
   Gaussian sampling, and exact SVD as primitives. The algorithm must be
   a uniform finite operational procedure using those primitives, not an
   arbitrary function secretly reading `A` or an uninterpreted
   `RunsInQueries` label. All finite loops and tie rules terminate;
   exceptional rank-deficient or zero-sketch outcomes have defined output.

Only oracle calls are charged. Candidate scans, processing of oracle
answers, construction of dense intermediate matrices, exact SVD of an
`a × b` matrix (conventionally `O(ab min(a,b))` arithmetic operations),
Gaussian draws, and other exact-real arithmetic do **not** count toward
the query bound. No bit complexity, finite precision, bounded matrix norm,
streaming-memory, or total runtime guarantee is added. This is the
canonical model in README lines 20–22 and 44, and in the source's
introduction and model audit.

## Original existential and stronger resolved numerical target

Let `t = log(2M)` with natural logarithm. The original question asks for
absolute `C > 0`, an integer `b ≥ 0`, and one uniform algorithm such that
the committed schedule has length at most

```text
C · sqrt(t) · ε^(−2) ·
  (1 + log(2+t) + log(1/ε))^b
```

for every admissible input, and the output event above has probability
at least `99/100`. The same `C,b` and same algorithm precede **all**
dimensions, families, target matrices, and accuracies. The query bound
is worst-case over the algorithm's random plan, not merely an expectation
or a bound conditioned on success. The nonnegative integer `b` admits
`b=0`; the bracket then equals one.

The source proves a stronger, explicit theorem. Record it as a named
companion to the original existential `Target`:

```text
one uniform fully nonadaptive algorithm;
queryCount ≤ 4,000,000 · sqrt(log(2M)) · ε^(−2);
Pr[‖A-B‖_F ≤ (3+ε) OPT(A,𝓕)] ≥ 99/100.
```

Thus the original has `C=4,000,000` and `b=0`. Source Theorem 1.1 gives
the slightly stronger probability `≥ 1−0.008151 > 0.99`; this may be a
further named numerical companion, but the canonical threshold `99/100`
must remain visible. Both bounds are exact real inequalities, not rounded
query counts. The count itself is a natural number. There is no extra
polylogarithmic factor in the resolved count.

## Source witness and edge cases

The source's algorithm sets `L=ceil(log₂(2M))`, `r=ceil(sqrt L)`,
`η=ε/4`, and fixed widths `s,k,ℓ`, with `N=s+k+ℓ`. If `n≤N`, it
prequeries the `n` standard basis vectors on the right, recovers all of
`A`, and returns an exact nearest family member. Otherwise it prequeries
two mutually independent right Gaussian blocks (`s+k` columns total)
and one independent left Gaussian block (`ℓ` columns), then performs all
selection and low-rank repair using stored answers. The source counts
`min(n,N)` queries and proves `N≤3,187,344 sqrt(t) ε^(−2)`, strictly
below the advertised `4,000,000` bound (Section 5). Its SVD construction
uses the **actual** rank of a sketch, handles rank zero, and uses a
pseudoinverse; its `OPT=0` argument yields exact return almost surely
(Section 2). These are proof witnesses and model checks, not additional
promises restricting the public input domain.

The target is the nonadaptive `(3+ε)` finite-family result. It does not
claim the stronger nonadaptive `(1+ε)` relative-error question, a bound on
arithmetic work or mantissa bits, or a result for an infinite family.
