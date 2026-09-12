# RA-07: exact numerical and semantic targets before proof

This statement-first package concerns the complete original discrete-convexity
question in [canonical RA-07](../README.md), at upstream commit
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. The complete informal source is
Matthew J. Colbrook's [Convexity of a volume-sampling error sequence](../../../references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex),
Theorem 1.1 and its proof. Its sampling, Jensen and stable-rank applications
are not part of the canonical question and are outside this formalization.
The source's strict monotonicity and additional second difference at index 1
are likewise not claimed by the final target.

Formalization author: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA, with AI assistance. Mathematical source authorship remains
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge. No George email is included.

**Stage 1 only.** The Challenge contains intentional placeholders and establishes
no theorem. Two independent statement approvals must precede any implementation.
The planned proof path below is a list of obligations, not assumed evidence.

## Complete canonical target

For every natural number `n ≥ 3`, every `λ : Fin n → ℝ` with
`∀ i, 0 < λ i`, define

\[
e_j(\lambda)=\sum_{\substack{S\subseteq\{0,\ldots,n-1\}\\|S|=j}}
  \prod_{i\in S}\lambda_i,
\qquad F_j=(j+1)e_{j+1}(\lambda)/e_j(\lambda).
\]

The final theorem asserts, without further hypotheses,

\[
F_{j-1}-2F_j+F_{j+1}\ge0
\quad\text{for every integer }2\le j\le n-1.
\]

`elementarySymmetric` is the actual finite-subset sum, using
`Finset.univ.powersetCard` and `Finset.prod`; it is not defined as a polynomial
coefficient or a presumed expectation. `errorSequence` uses the ordinary real
division of that sum. `ConvexityConjecture` preserves the original quantifier
order and weak inequality. There is no normalization, sorting, distinctness,
upper or lower numerical cutoff, generic-position assumption, or preassigned
root factorization. Fin's indices are zero-based; this changes no subset.

The definition is total for natural indices, but only the canonical index range
is asserted. The `elementary_values` export must prove, from positivity alone,

\[
e_0=1,\qquad e_j=0\ (j>n),\qquad e_j>0\ (0\le j\le n).
\]

Thus every denominator actually used by the target is positive. In particular,
`e_(n+1)=0`, `e_n>0`, and `F_n=0` follow from the real subset definition rather
than being extra input conventions. Natural subtraction in `j-1` and `n-1`
cannot truncate a relevant positive index because `n≥3` and `j≥2`.

## Actual generating polynomial and derivatives

Define the real polynomial

\[
P_\lambda(t)=\prod_{i=0}^{n-1}(1+\lambda_i t),
\qquad Q_d=P_\lambda^{(d)},
\]

using actual `Polynomial.C`, `Polynomial.X`, multiplication and
`Polynomial.derivative` iterated `d` times. For every real tuple (even without
positivity) and every natural `j`, `generating_derivative_values` must prove

\[
[t^j]P_\lambda=e_j(\lambda),\qquad
Q_j(0)=j!e_j(\lambda).
\]

In particular, the bridge
`F_j = Q_(j+1)(0)/Q_j(0)` must be derived using the real factorial identity
and the positive denominators; it is not a definition or premise of convexity.
Mathlib already supplies `Finset.esymm_map_val` for the identical subset sum
and `Polynomial.coeff_iterate_derivative` for actual derivatives. These should
be reused where useful instead of assuming the coefficient identities.

For every positive tuple and `0≤d≤n`, the unconditional export
`positive_derivative_factorization` requires

\[
Q_d(0)>0,\quad \deg Q_d=n-d,\quad
\exists\mu:\operatorname{Fin}(n-d)\to\mathbb R:\quad
(\forall a,\mu_a>0)\ \land\
Q_d(t)=Q_d(0)\prod_a(1+\mu_a t).
\]

Polynomial equality is equality of the actual polynomials. Exactly `n-d`
factors preserve all root multiplicities, including repeated input numbers
and repeated derivative roots. No root list, real-rootedness predicate, split
hypothesis, or factorization identity is an input to this export. At `d=n`,
the product is empty and `Q_n` is a positive constant. Its degree is zero;
the theorem does not apply a nonconstant-root lemma to that derivative.

The planned structural proof may embed these polynomials into `ℂ[X]` and use
Mathlib's actual Gauss–Lucas theorem
`Polynomial.rootSet_derivative_subset_convexHull_rootSet`. The strictly negative
real axis is convex, so it contains the derivative roots if it contains the
original roots. Complex splitting and the actual root multiset then give the
factorization, including multiplicities. Each derivative's nonzero value at
zero and degree must be established; root-set inclusion alone does not prove
the correct number of roots or allow replacing multiplicities by distinct roots.
Passing back to a real polynomial and setting `μ_a=-1/r_a>0` must be proved.
This route replaces the source's repeated Rolle argument with an existing
formal theorem; neither route may leave real-rootedness as an assumption.

## Exact scalar certificate, without numerical approximation

For `μ : Fin m → ℝ`, put

\[
s_r=\sum_a\mu_a^r,\quad
G(\mu)=\sum_{a<b}\mu_a\mu_b(\mu_a-\mu_b)^2,\quad
D(\mu)=s_1(s_1^2-s_2).
\]

`pairGap` sums exactly once over each pair by the genuine strict order on
`Fin m`; `powerSum` and `certificateDenominator` use real sums and natural
powers. For every `m≥2` and every positive tuple `μ`, the unconditional
`power_sum_certificate` requires

\[
D(\mu)>0,\qquad s_1s_3-s_2^2=G(\mu),\qquad G(\mu)\ge0.
\]

Denominator positivity must use
`s_1²-s_2 = 2∑_(a<b) μ_a μ_b > 0`; there are at least two positive factors.
The gap may be zero, including all-equal input cases. Strict convexity is not
asserted. The pair identity is an exact finite-sum identity, with no limiting,
floating-point, sampling or interval estimate.

For the canonical index `j`, take derivative order **`d=j-1`**, hence
factor count **`m=n-(j-1)=n-j+1`**. The distinction between derivative order
and second-difference index is essential. The first three actual derivative
values of the factored polynomial give

\[
\begin{aligned}
Q'(0)/Q(0)&=s_1,\\
Q''(0)/Q(0)&=s_1^2-s_2,\\
Q'''(0)/Q(0)&=s_1^3-3s_1s_2+2s_3.
\end{aligned}
\]

These identities must be proved from actual polynomial differentiation, not
substituted for it. Together with the coefficient bridge they imply

\[
F_{j-1}=s_1,\quad
F_j=(s_1^2-s_2)/s_1,\quad
F_{j+1}=(s_1^3-3s_1s_2+2s_3)/(s_1^2-s_2).
\]

The `second_difference_certificate` export must, from only the canonical
dimension/index/positivity assumptions, produce such a positive tuple `μ`,
its exact factorization of `Q_(j-1)`, its positive denominator, and the equality

\[
F_{j-1}-2F_j+F_{j+1}=2G(\mu)/D(\mu).
\]

Thus the certificate is tied to the actual elementary symmetric sums. A generic
conditional lemma assuming this factorization or scalar equality would not
prove this export or the canonical assertion.

At the upper endpoint `j=n-1`, **`m=2`**, `Q'''=0` and `F_(j+1)=F_n=0`.
The third-derivative expression must still vanish and the denominator stays
strictly positive. At the smallest canonical dimension `n=3`, the only index
is `j=2`; this is precisely that degree-two endpoint. Repeated roots and
all-equal spectra are included with no perturbation or excluded set.

## Computation and trust policy

No instance of this theorem reduces to a finite numerical witness: its inputs
are all positive spectra in all dimensions. The requested computation reduction
is therefore exact analytic algebra, leaving **no interval boxes, sample grid,
floating-point eigenvalues, or artificial numerical point certificate**.
LeanCert is pinned with Lean 4.33.1 and will supply kernel trust auditing for
the completed exports. Following the shared guide, pure algebra needs no
decorative interval calculation. Any additional numerical certificate introduced
later must be reviewed, use explicit kernel mode, and participate in the full proof.

The final proof may depend only on `{propext, Classical.choice, Quot.sound}`
or a subset. No custom axiom, native-execution trust, proof hole, or imported
Challenge is permitted in the completed Solution. All six public signatures
will be selected by Comparator with an empty `definition_names` list. The
Challenge's six deliberate placeholders are isolated and will never count as
proofs. Local compilation, two final independent reviews and actual Linux
Comparator/kernel replay remain separate later gates.
