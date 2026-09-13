# Proof review guide

## Status and target

This guide identifies proof obligations in the accompanying unreviewed
manuscript. It is not an independent review. The claimed result is a pair of
bounds with an unresolved factor of depth, not a matching characterization.

The exact target is a proper HODLR output, on the prescribed partition, with
Frobenius error at most `(1+epsilon) OPT` with probability at least 0.99 for
**each fixed input**. Both forward and transpose vector queries are charged.
The lower bounds allow randomized measurable adaptive choices and unrestricted
measurable postprocessing. The upper bounds assume the exact-real model in the
problem statement.

## Dependency map

**Upper bound (Theorem 7.3).** Separable block optimum → deterministic truncation
inequality (Lemma 3.1) → row-isotropic consequence (Corollary 3.2) and Gaussian
least-squares moments (Lemma 3.3) → noisy Gaussian block estimate (Theorem 4.1)
→ contamination accounting and global pilot error (Section 5) → accurate
retained ranges (Section 7.1) → shared-regression row isotropy (Lemma 7.1)
→ conditional proper-fit risk (Proposition 7.2) → expectation-to-probability
conversion and explicit query budget (Theorem 7.3).

**New lower bound.** Adaptive iid-Gaussian transcript divergence (Lemma 8.1)
+ weighted finite frame packing (Lemma 9.1) + selected-column anchor loss
(Lemma 10.1) → a finite decoding problem and Fano's inequality →
`Omega(k(L-4)/epsilon)` in the core regime (Proposition 10.2).

**Earlier accuracy term.** Adaptive shifted-GOE divergence + local projector
loss + finite projector packing → `Omega(k/epsilon**2)` in the core accuracy
regime → monotonicity and the exact-recovery obstruction extend the bound to
`Omega(min(n,k/epsilon**2))` (Appendix A).

**Combination.** Section 11 treats the complement of the depth core using the
accuracy bound, combines the two capped lower terms, and invokes Theorem 7.3.
The exact obstruction `k(L+1)` and the `n`-query baseline are separate arguments.

## Highest-priority audits

### 1. Shared-regression symmetry is a joint statement

Condition on the entire pilot and use a fresh Gaussian sketch. For a retained
block `(I,J)`, every column design indexed by `J` contains the same embedded
basis `Q_b`. Every other design component for those columns has support outside
`I`, and every residual column is orthogonal to `Q_b`. Consequently the common
Gaussian design `Omega.T @ Q_b` is independent of all the other components and
all residual responses for these columns simultaneously.

Rotating this one common design on the right rotates the coefficient **error**
on the left. The true coefficient matrix need not be rotationally invariant:
it cancels when the regression error is formed. This gives row-isotropic
second moments, not independence between fitted columns or different blocks.
Check both this invariance and the trace identity with the individual full
column-design dimensions `r_j` in the denominators.

### 2. No data-dependent basis is treated as independent of its own sketch

The noisy block estimate conditions on a right range sketch before using an
independent left sketch. Both orientations at a level use the same frozen
coarser pilot. The final global regression is independent of the entire pilot.
The known-rank-k-space result in Section 6 is conditional and cannot be used
without paying for those spaces. A full-matrix SVD helper appears in tests only.

### 3. Contamination and depth factors are not silently discarded

At each level, the right and left hash collisions each charge coarser residual
entries at most once after summing the two orientations. Averaging gives
`T_past/B` separately for each side. The two contamination energies are not
asserted to be mutually independent. The global pilot calculation uses
`sum E T_past <= h S` with `B=h`, where `h=L-1`.

For the final shared fit, each residual column enters exactly one sibling
column interval per nonterminal level. This is why `sum S_b <= h R_Q**2/d`,
and why a depth factor remains in the final truncation bound. Removing it would
need a new argument; it has not been removed by a notation change.

### 4. Truncation, ranks, and zero optimum

The deterministic inequality must hold without a singular-value gap or a
noise-distribution assumption. In its proof, right-singular projectors are
used to obtain an orthogonal error decomposition. Check the cross-term
coefficient and the final `6 ||E||_F**2` bound.

The retained bases may have fewer than `k` columns or be zero. These cases are
handled separately. Size-`2k` diagonal blocks are unrestricted by the original
recursive rank condition, so they can be fitted without extra rank loss.
The final rank-k truncation occurs on the genuine constrained blocks. Properness
makes excess loss over `OPT**2` nonnegative. This is essential to the Markov
step yielding the 0.99 guarantee. `OPT=0` is handled by zero expected error,
not by dividing by the optimum.

### 5. Adaptive Gaussian conditioning and both oracle sides

Maintain separate spans of forward query vectors and transpose query vectors.
At a fixed history and fixed hypothesis, the unexposed iid-Gaussian component
is an isotropic Gaussian on the corresponding rectangular complement. A fresh
query is orthogonalized only against its own side's span; the part of the
response known from the other side is removed. Redundant steps reveal no new
information. The argument must hold for regular conditional laws under all
measurable adaptive choices, not merely deterministic or fixed queries.

For the GOE proof in Appendix A, the unexplored matrix is symmetric and the
new scalar diagonal response has variance twice that of an off-diagonal
response. The two normalizations must not be interchanged.

Known invertible right scaling `D` preserves the ability to simulate either
oracle type with one query. It does not preserve Frobenius loss. The loss of
the scaled family is analyzed explicitly in Section 10.

### 6. The hierarchical packing is finite and uniformly separated

Selected column sets at distinct target nodes are disjoint. Fine-to-coarse
orthogonality makes all nonzero columns of `S` orthonormal, so `||S||_op=1`.
The available dimension is `15m/16+k`, not the full ambient block size `m`.
The small-cap bound is uniform in finer frames and in previously exposed
columns. The conditional bounds must be integrated in the order stated before
performing the greedy finite packing argument.

The floating-point generator produces continuous random frames. Those samples
verify geometry but do not establish cardinality or separation of the finite
packing used in Fano's inequality.

### 7. Anchors and decoding

The anchors are fixed before the random label and Gaussian perturbation are
chosen. Their magnitude may be arbitrarily large in the stated arithmetic
model. They occupy only the selected columns of each true sibling block, so
the clean family is in the rank-constrained class. The selected columns must
remain full rank on the good-noise event, uniformly over labels.

Only the output's proper rank constraint links its selected and unselected
columns. Subtracting the fixed anchor gives a decoder for the weighted signal,
not for the Gaussian noise. The selected-entry noise has a smaller expectation
than the entire weighted noise; these are separate quantities. The core
condition `epsilon*(L-4) >= 1` is needed before absorbing the former into the
radius bound.

### 8. All-parameter extension and caps

The depth core has `L>=8` and `epsilon*(L-4)>=1`. Outside it,
`kL/epsilon <= 4k/epsilon**2`, so the earlier accuracy bound supplies the missing
depth lower bound. In the core the uncapped depth expression is at most `n`.
The accuracy proof is first established at very small epsilon and sufficient
ambient dimension, then extended by monotonicity and exact recovery. Do not
apply the published `Omega(kL+k/epsilon)` result outside its stated dimension
regime as a substitute.

## What the numerical suites do and do not test

The tests include deterministic inequalities, finite Gaussian posterior
identities, Monte Carlo moment calculations, algebraic parameter checks,
continuous packing geometry, and oracle-only implementation exercises. They
can expose algebraic or implementation mistakes. They cannot prove a uniform
probability statement, all measurable adaptive conditioning, a finite packing
entropy bound, exact-real arithmetic behavior, or the missing matching theorem.

The rank-one short-sketch nullspace example is a deterministic obstruction to
an embedding that holds simultaneously for all candidates. Its witness depends
on the sketch. Treating it as a lower bound against the fixed-input randomized
model would reverse the required quantifiers.

## Remaining mathematical task

Prove a general oracle algorithm with `O(min(n,kL/epsilon+k/epsilon**2))`
queries, or prove a stronger lower bound and a matching upper bound. The
conditional coefficient solver, a generic assertion of better joint fitting,
and the sketch-dependent nullspace example do not accomplish either task.
