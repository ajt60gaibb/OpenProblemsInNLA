# TR-07: complete original asymptotic target

## Source, credit, and scope

The canonical source revision is
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The files in
`randomized-and-low-rank-approximation/TR-07/` have SHA256 hashes:

| File | SHA256 |
| --- | --- |
| `README.md` | `1f2b4c9bfd606f49d2c522483a7375cff104744e7a540db1613bb01f91a281d0` |
| `solution.tex` | `207eb87c6b47d3a3a1a529c49b7c5a4dcaf099a942d60fdc1b9b5e3285aae7a0` |
| `solution.md` | `307e8b419a4eb453e789120d86e1344b2aecaf8a8ce759f87d9585a470496fee` |

The complete informal proof is `solution.tex`, not the short Markdown
pointer. Sidney Holden, Center for Computational Biology, Flatiron Institute,
Simons Foundation, New York, USA, receives mathematical-resolution credit.
Han Huang, Mark Rudelson, and Konstantin Tikhomirov retain the conjecture and
prior-result credit in the canonical page. The new formalization is authored
by OpenAI Codex agents. No human or source-author endorsement is asserted.

The target is the entire original asymptotic statement (the source's
Corollary 1.2). Its stronger exponential finite tail bound and positive
fraction of small singular values are not required by the original problem
and are not advertised as formalized results.

## Quantifiers, dimensions, and probability

For every fixed natural number `s >= 2`, every finite real `C >= 1`, and
every pair of sequences `r n : Nat -> Nat`, assume `r k <= k`, `r k <= n k`,
`k / r k -> C`, and `n k / r k -> +infinity`. The ratios use real division.
For every deterministic matrix sequence
`M k : Matrix (Fin k) (Fin (n k)) Real` whose entries are in `{-1,0,1}`
and whose columns each have exactly `s` nonzero entries eventually, and for
every fixed real `eta > 0`, prove

```
Pr { smallestSingular ((M k) restricted to I) > eta } -> 0.
```

Here `I` is uniform over **all subsets of column indices of cardinality
`r k`**. The probability in `subsetTail` is precisely the real ratio of
the number of subsets satisfying the strict inequality to the number of
all such subsets. Repeated column values retain their multiplicities in
this sampling law. There is no assumption about intersections of supports,
entry signs, matrix independence, or any distribution on `M`.

The explicit condition `r k <= n k` states the domain of the original
uniform subset experiment. Allowing sparsity only eventually removes
irrelevant initial dimensions `k < s`; it strengthens the conclusion's
scope rather than hiding a new premise. No positive sample size is imposed
at `k = 0`. The finite positive limit of `k/r k` with `C >= 1` forces
`r k > 0` and indeed `r k -> infinity` eventually; these facts must be
proved, not assumed. Together with `n k / r k -> infinity`, they force
`r k / n k -> 0`.

## Norm and singular-value semantics

`Vec k` and the selected coefficient space `EuclideanSpace Real I` use
the Euclidean norm. `selectedAction` is the literal rectangular matrix
product, with its output represented in Euclidean space; no entrywise or
row-sum matrix norm is substituted.

`smallestSingular M I` is the real infimum of the set of values
`norm (selectedAction M I x)` over **every** vector `x` of norm exactly
one. Lean's real infimum of the empty set is zero. This convention only
affects the empty selected set, which is excluded eventually by the
ratio hypotheses, so it cannot affect the asserted limit. The proof must
justify every use of the infimum, including boundedness and nonemptiness
where needed. The tail event is strictly `eta < smallestSingular`.

The single advertised declaration is
`NLA.TR07.random_column_subsets : NLA.TR07.SolvesTR07`. `SolvesTR07`
expands to precisely the quantifiers above. Comparator compares separate
`Challenge` and `Solution` modules, has no replaceable definition holes,
and permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Planned proof reductions and numerical constants

All supporting certificates must be proved and connected to the concrete
subset probability above. No asymptotic estimate or reconstruction oracle
is an input assumption. The following describes the planned proof route;
auxiliary constants may be weakened without changing the frozen target.

Use the minimum number of column deletions needed to leave an
`eta`-bounded-below column restriction. This integer is one-Lipschitz under
single-column replacement. A matrix with least singular value greater
than `eta` has deletion number zero. If `m` distinct center columns can
each be reconstructed from a disjoint common reservoir to error at most
`eta/2`, rank-nullity and Bessel's inequality give deletion number at least
`m/2`. Reconstruction coefficients need not be bounded, and reservoir
columns may be shared by the witnesses.

For a column law with incidence probabilities `p_i`, use the regularized
positive diagonal `D_i = p_i + 1/k` (in positive dimension) and covariance
`Sigma`. The polynomial filter is `(I - Sigma * D^(-1) / s)^L`. Since
`Sigma <= s*D`, its positive semidefinite conjugate
`R = D^(-1/2) * Sigma * D^(-1/2)` has spectrum in `[0,s]`, and
`trace D = s+1`. The average squared filter residual is at most
`s*(s+1)/(2*L+1) <= 2*s^2/(2*L+1)`. No Euclidean contraction of the
possibly nonsymmetric filter is assumed.

Unlike the source's pruning construction, this regularization uses the
whole column law and includes an absorbing zero state. From a nonzero
signed column state `v`, choose `i` uniformly in its support. With
probability `p_i/(p_i+1/k)` draw `w` conditionally on `w_i != 0` and move
to `v_i*w_i*w`; otherwise move to zero. Zero stays zero. The mean
transition is still `Sigma * D^(-1) / s`, and every state has squared norm
at most `s`. There is no assumed sign symmetry.

Finite signed trajectories realize the polynomial mean. With
`epsilon = eta/2`, sufficient choices are
`L = ceil(8*s^2/epsilon^2)`, `S = 2^L-1`,
`b = ceil(8*s*S^2/epsilon^2)`, and `J = b*L`.
Equivalent existential natural bounds are allowed: only finiteness,
positivity, and the error inequalities are used. Averaging `b` independent
length-`L` trajectories conditional on the center gives mean squared
reconstruction error at most `epsilon^2/4`, so the ideal success probability
is at least `3/4`. All parameters depend only on `s, eta`, before dimensions
or matrix entries.

For a fixed aspect lower bound `0 < beta <= 1` and `beta*k <= r <= k`,
take `floor(r/2)` centers and `J` reservoir chunks of length
`ell = floor((r-floor(r/2))/J)`. When `r >= 4*J`,
`r/(4*J) <= ell <= k`. At each nonzero-state transition, with probability
`1/2` output zero; otherwise take the first vector in the next chunk whose
requested coordinate is nonzero, failing if there is none. For incidence
`0 <= p <= 1`, its hit probability satisfies

```
1-(1-p)^ell >= ell*p/(1+ell*p) >= (ell/k)*p/(p+1/k).
```

Thus the **unnormalized** successful transition kernel dominates `a` times
the ideal kernel, with `a = beta/(16*J+beta) > 0`, both for the zero
outcome and for signed nonzero outcomes. Conditioning on all hits must
not be asserted to preserve the ideal law: the hit probabilities depend
on the path. Composing nonnegative kernels gives a reconstruction
probability at least `(3/4)*a^J` per center. Shared-reservoir witnesses and
linearity of expectation give expected deletion number at least `rho*r`
for some fixed `rho > 0`; `rho = (3/32)*a^J` is a sufficient conservative
choice. Absorbing zero outcomes are valid reservoir linear combinations.

Concentrate the deletion number for independent column-index draws using
a variance bound at most `r`. Repair repeated indices to obtain a uniform
ordered sample of distinct indices. The expected number of repairs is
`r*(r-1)/(2*n)`. Chebyshev's and Markov's inequalities then give, for the
unordered uniform subset law, a sufficient tail bound

```
4/(rho^2*r) + (r-1)/(rho*n).
```

An equal-fiber counting or equivalent probability argument must connect
the ordered injective sample to the exact `powersetCard` ratio in the
definition. Column order does not change the singular-value event.
Finally use `beta = 1/(2*C)` and the ratio hypotheses to make the bound
tend to zero. This polynomial tail is sufficient for the entire original
target. No claim is made to the source's stronger exponential estimate.

No floating-point computation, approximate spectrum, interval oracle,
native execution axiom, unproved certificate, restricted dimension, or
favorable sampled event may support the exported theorem.
