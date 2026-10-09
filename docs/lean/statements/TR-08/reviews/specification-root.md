# TR-08 independent specification review

**Verdict: APPROVE** for Lean statement implementation. The specification
was authored by `/root/inventory_review`; I independently compared it with
the full canonical page and source proof. This is a pre-implementation
source review, not a Lean-boundary or proof verification result.

## Inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/TR-08/README.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/ORIGINAL.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/NUMERICAL_TARGETS.md` | `e54b57685e9b28bb9703d2195d38de6f861e288ba8762b596b1480abfd9ea84e` |
| `randomized-and-low-rank-approximation/TR-08/solution.tex` | `90af48e5fdeb3f3efca0eea5763d8c5a2171a67e4db96145e59e7601d3c82009` |

`ORIGINAL.md` matches the canonical README byte for byte. The source
Theorem 1.1 and final equivalence proof (especially lines 67–103 and
511–519) support the stated full sequence criterion.

The specification retains row dimensions tending to infinity only through
positive multiples of 100, every fixed ambient growth exponent `c>0`,
arbitrary admissible ambient column and sparsity sequences, independent
columns with exactly `s_k` distinct uniform row locations, independent
fair signs of magnitude `1/sqrt(s_k)`, and an independent uniform subset
of exactly `k/100` selected columns. The probability includes both draws;
the solution's smaller product-law model is justified only by this
exchangeability reduction. No Bernoulli support or with-replacement model
is substituted.

The target event is a weak lower bound on the true least singular value,
for one fixed positive `a` along the whole sequence. The right criterion
is positive `liminf s_k²/log k`, equivalently an eventual lower bound by
some positive multiple, with no monotonicity assumption. The specification
includes oscillating sequences, the critical square-root-logarithm window,
and the source's optional explicit `a(h)` witness without promoting it to
an input assumption. No upper distortion target or numerical optimizer
claim is introduced. I found no substantive mismatch; the complete Lean
law, asymptotic semantics and import closure still require separate review.
