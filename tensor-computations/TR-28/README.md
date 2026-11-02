# TR-28 — Entropy formula for the asymptotic subrank of Dicke tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-11-02

**Rating rationale:** Matching the entropy upper bound for this structured tensor family requires substantial progress beyond its known binary and multilinear cases. Tensor restriction rates and entanglement conversion give the question community importance. These ratings are historical and refer to the original question, which is resolved below.

## Resolution — 2 November 2026

**Resolved affirmatively.** Wenqi Zhu (University of Oxford), Chunlin Liu
(University of Science and Technology of China), Kai Zou (King's College
London) and Ping Nie (University of Waterloo).

For every $`n\ge2`$ and every tuple $`\mathbf d=(d_1,\ldots,d_n)`$ of positive
integers, with $`k=d_1+\cdots+d_n`$ and $`H`$ the base-two entropy of the
problem statement below,

```math
\widetilde Q(D_{\mathbf d})=2^{H(d_1/k,\ldots,d_n/k)},
\qquad
Q(D_{\mathbf d}^{\boxtimes N})\le k\,2^{N H(d_1/k,\ldots,d_n/k)}\quad(N\ge1).
```

This is Theorem 1.1, stated on p. 2 of the 13-page paper
[*The Entropy Law for the Asymptotic Subrank of Dicke Tensors*](https://github.com/erenup/dicke-tensor-subrank/blob/e344c05618a8a76941fc6dc166b22ed54384f6cf/paper/main.pdf)
at the immutable
[revision `e344c05`](https://github.com/erenup/dicke-tensor-subrank/tree/e344c05618a8a76941fc6dc166b22ed54384f6cf),
dated 2 November 2026. Lemma 3.1 (p. 3) proves that the limit defining
$`\widetilde Q(D_{\mathbf d})`$ exists, and Section 3 settles the two-factor
case. For $`k\ge3`$ the lower bound is obtained by coordinate restrictions in
Sections 4–9 and completed at the end of Section 9 (p. 10). The upper bound, for arbitrary linear maps and every power $`N`$, is
Proposition 10.3 (p. 11), proved by a slice-rank cover.

**Comparison with the target.** The paper's $`D_{\mathbf d}`$ is the displayed
sum of basis tensors, with no scalar factor. Its subrank $`Q(T)`$ is the
largest $`q`$ for which complex linear maps $`A_i:V_i\to\mathbb C^q`$, chosen
independently for the $`k`$ factors, satisfy
$`(A_1\otimes\cdots\otimes A_k)T=\sum_{j=1}^q e_j^{\otimes k}`$, with no
symmetry or coordinate constraint, and
$`\widetilde Q(T)=\lim_{N\to\infty}Q(T^{\boxtimes N})^{1/N}`$ for the power
that groups corresponding factors and retains exactly $`k`$ factors. These are
the definitions of the problem statement. The paper writes the value as
$`\exp H(p)`$ with $`p_a=d_a/k`$ and natural logarithms; this equals
$`2^{H(d_1/k,\ldots,d_n/k)}`$ in the base-two notation used here. The theorem
holds over $`\mathbb C`$ for every $`n\ge2`$ and every tuple of positive
integers, so it covers the full range of the target, including the previously
known cases $`n=2`$ and $`d_1=\cdots=d_n=1`$. All $`k`$ original modes remain
separate. The limit is pointwise in each fixed $`\mathbf d`$; the theorem gives
no rate uniform in $`\mathbf d`$, no finite-subrank equality, and no statement
about tensor rank, border rank or tensors with merged modes, none of which the
target asks for.

**Coordinate restrictions and Question 1.58 of reference 3.** Theorem 1.1
also proves that $`\widetilde Q_{\mathrm M}(D_{\mathbf d})`$, defined in the
same way using only deletion of local basis vectors followed by independent
relabelling and nonzero rescaling, has the same value. Since
$`\widetilde Q_{\mathrm M}\le\widetilde Q`$, this strengthens the lower bound.
Question 1.58 of reference 3 concerns a monomial rate defined by monomial
degeneration (Definition 1.18 there; Remark 1.12 there distinguishes it from
the rate defined by monomial restriction), not by this coordinate-restriction
limit. Equation (2.1) of the paper places that rate between
$`\log_2\widetilde Q_{\mathrm M}(D_{\mathbf d})`$ and
$`\log_2\widetilde Q(D_{\mathbf d})`$, using the equivalence of restriction and
degeneration for the ordinary rate (Theorem 1.11 of reference 3), so the
theorem also answers that question; no general equivalence of the two
monomial notions is used. The catalogue target concerns ordinary subrank only and does not
depend on this comparison.

**Proof and verification scope.** Theorem 1.1 is proved in the written paper.
A Lean formalization at the same revision proves only ten universal finite
algebraic and combinatorial targets, recorded in its
[formal scope](https://github.com/erenup/dicke-tensor-subrank/blob/e344c05618a8a76941fc6dc166b22ed54384f6cf/lean/SCOPE.md):
three partner-count identities, exact-span partner containment and its count
bound, a finite-field kernel count, the isolation count, exact coordinate
extraction, finite uniform isolation, and an abstract dimension bound for
invariant supermodular functions. The entropy inequality, including the
supermodularity of quotient entropy and its application to the permutation
action, the multinomial and average-free estimates, the transfer
of ranks to prime fields, the hashing probabilities, the tensor interpretation
of isolation, the existence of the limits, the asymptotic lower bound and the
slice-rank upper bound are proved in the text only. No Lean theorem states the
entropy formula, so this is not a Lean verification of the target. The
[verification record](https://github.com/erenup/dicke-tensor-subrank/blob/e344c05618a8a76941fc6dc166b22ed54384f6cf/VERIFICATION.md)
also describes exact checks of finite instances, which do not establish the
theorem.

**Review.** Solved by two independent informal AI-agent audits of the written
statement, proof and exact checks, both accepting the proof; the one
correction requested, to the comparison with the convention of Question 1.58
of reference 3, is incorporated. The complete argument was also checked by
coauthor Wenqi Zhu (University of Oxford). Chunlin Liu (University of Science
and Technology of China), a coauthor working on entropy, reviewed the proof.
The [review record](https://github.com/erenup/dicke-tensor-subrank/blob/e344c05618a8a76941fc6dc166b22ed54384f6cf/verification/reviews/README.md)
contains the audit reports. The paper discloses its use of AI tools. The
catalogue did not rerun the Lean or exact checks.

The retained status check below predates this resolution.

## Problem statement

Let $`n\geq2`$ and let $`d_1,\ldots,d_n`$ be positive integers with $`k=d_1+\cdots+d_n`$. In $`(\mathbb C^n)^{\otimes k}`$, define the Dicke tensor

```math
D_{\mathbf d}=
\sum_{\substack{(i_1,\ldots,i_k)\in\{1,\ldots,n\}^{k}\\
|\{j:i_j=a\}|=d_a\ \text{for all }a}}
e_{i_1}\otimes\cdots\otimes e_{i_k}.
```

For any tensor $`T\in V_1\otimes\cdots\otimes V_k`$, its subrank $`Q(T)`$ is the largest integer $`s`$ for which there are linear maps $`L_j:V_j\to\mathbb C^s`$ satisfying

```math
(L_1\otimes\cdots\otimes L_k)T=\sum_{a=1}^{s}e_a^{\otimes k}.
```

Let $`\widetilde Q(T)=\lim_{m\to\infty}Q(T^{\boxtimes m})^{1/m}`$, where powers group corresponding modes.

Does every Dicke tensor satisfy

```math
\widetilde Q(D_{\mathbf d})
=2^{H(d_1/k,\ldots,d_n/k)},\qquad
H(p_1,\ldots,p_n)=-\sum_{a=1}^np_a\log_2p_a?
```

The maps in the subrank definition are arbitrary complex linear maps, independently chosen in each mode. No symmetry or coordinate-selection constraint is imposed. Multiplying $`D_{\mathbf d}`$ by a nonzero scalar does not change the question, so this agrees with the symmetric-tensor convention for the monomial $`x_1^{d_1}\cdots x_n^{d_n}`$.

## Why it matters

Subrank measures how many independent scalar computations a tensor can perform after linear transformations. The conjecture predicts the exponential rate obtainable from repeated copies of an explicit structured tensor solely from its multiplicity distribution.

## References and status check

1. P. Vrana and M. Christandl, *Asymptotic entanglement transformation between W and GHZ states*, [arXiv:1310.3244](https://arxiv.org/pdf/1310.3244), §VI, equation (40), p.10; Journal of Mathematical Physics **56** (2015), 022204. The conversion-rate formulation is reciprocal to the base-two logarithm of asymptotic subrank.
2. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), Conjecture 4.26, states the displayed subrank formula explicitly.
3. M. Christandl, P. Vrana, and J. Zuiddam, *Asymptotic tensor rank of graph tensors: beyond matrix multiplication*, [Computational Complexity **28** (2019), 57–111](https://ir.cwi.nl/pub/28609/28609.pdf), introduction and tight-tensor lower-bound results.

### Status check — 2026-09-10

Checked the source formulation and the explicit 2025 restatement, Conjecture 4.26, with targeted Dicke-tensor/subrank/entropy searches through 2026. The formula is established for $`n=2`$ and for $`d_1=\cdots=d_n=1`$, substantive parameter families within this target. The all-multiplicity statement remains conjectural in the survey, and no full later resolution was located. Asymptotic-rank computations and lower bounds on subrank do not by themselves establish the requested equality.
