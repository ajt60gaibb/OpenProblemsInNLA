# TR-08 independent pre-implementation specification review

Reviewer: `/root/fr05_review`, independent of the specification author.
Verdict: **APPROVE** for Lean statement implementation. This reviews the
exact target and source correspondence, not the proof of the threshold.

## Reviewed inputs and SHA-256

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/TR-08/README.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/ORIGINAL.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/NUMERICAL_TARGETS.md` | `e54b57685e9b28bb9703d2195d38de6f861e288ba8762b596b1480abfd9ea84e` |
| Source, `randomized-and-low-rank-approximation/TR-08/solution.tex` | `90af48e5fdeb3f3efca0eea5763d8c5a2171a67e4db96145e59e7601d3c82009` |

`ORIGINAL.md` is byte-identical to the canonical README (`cmp` exit
status zero) at published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`.
The registry preserves the canonical path
`randomized-and-low-rank-approximation/TR-08/README.md`.

## Mathematical and numerical correspondence

Canonical README lines 31–41 and the source's statement/reduction section
specify `k → ∞` through multiples of 100, `n_k ≥ k^(1+c)` for fixed
`c > 0`, and `1 ≤ s_k ≤ k`, with no monotonicity. The specification
lines 10–21 preserves this entire sequence domain. Reindexing by
`k=100t`, `t≥1`, retains exactly the intended asymptotic sequence.

The original random law uses independent columns, each with a **uniform
size-`s_k` subset of distinct rows**, and independent fair signs of exact
magnitude `1/sqrt(s_k)` on its selected locations. The selected column
set has exactly `k/100` members, is uniformly sampled from the ambient
columns, and is independent of the matrix. Specification lines 23–55
preserves both random constructions and their joint probability. The
source proves the selected columns have the same product law as `k/100`
fresh columns, conditional on every selected index set; the spec correctly
requires that equality to be justified before using the reduced law.
No Bernoulli row inclusion or replacement sampling is introduced.

The least singular value in specification lines 57–70 is the infimum of
`‖Bx‖₂` over the real unit sphere, which is nonempty because `k/100≥1`.
The original asks only for a fixed positive **lower** singular-value
bound with probability tending to one. No upper norm condition is added.

Canonical resolution lines 17–25 and source Theorem 1.1 state exactly

```text
(∃ a>0, Pr{σ_min(B_k)≥a} → 1)
    ↔ liminf_{100|k, k→∞} s_k²/log k > 0.
```

Specification lines 72–108 preserves both directions, weak event
inequality, and quantifier order, including oscillating sequences. Its
eventual `∃ h>0` lower bound is equivalent to the positive `liminf`
since `log k>0` throughout the index range. A subsequence whose ratio
tends to zero therefore obstructs full-sequence convergence; the source
proves this in its final sequence section. The source's stronger uniform
`a(h)` and below-threshold convergence-in-probability statements are
properly labeled companions, not replacements.

The numerical witness in specification lines 119–123 agrees with source
equations `(J)`, `(constants)`, and `(a)`: `J(b)=b log(100b)−b+1/100`,
`η=J(1/32)/8`, `R=ceil(3/(ηh))+1`, `L=2(R−1)`, `D=1+128/h`, and
`a(h)=1/(6+8 sqrt(DL))`. The logarithms are natural. The witness need
not be computed to state the main equivalence. No mathematical or
numerical mismatch or pre-implementation blocker was found.
