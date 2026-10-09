# SP-14 counterexample: independent informal review

**Date:** 9 October 2026.

**Verdict:** PASS for the complete negative resolution of the original SP-14
target, with the limits stated below.

**Review type:** independent informal mathematical and source audit by an AI
agent (Claude, Anthropic, model Fable 5.1), run in a session separate from
the sessions that developed the argument and before reading the author's
self-audit. Not external human peer review; no Lean verification.

**Reviewed input:** `counterexample.tex`, SHA-256
`34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`
(2095 lines, 6 sections, Theorem 6.1), together with the saved primary sources
Bogoya–Böttcher–Grudsky 2012 and Böttcher–Fukshansky–Garcia–Maharaj 2015.
The scripts in `scripts/` import no submitted code.

## Target and sources

The canonical SP-14 statement, BBG 2012 §1 p. 2 ("canonically distributed
except when a extends analytically to an annulus r<|z|<1 or 1<|z|<R"), and
two further secondary statements found online (Basor–Morrison; arXiv:1807.01441,
introduction) agree: continuous symbol, both one-sided extensions absent, every
continuous compactly supported test function, no Jordan-curve hypothesis.
BFGM 2015, Section 3, eq. (6), p. 175, states Gohberg's theorem as strong
convergence of the finite-section inverses for piecewise continuous symbols
whose filled range avoids zero with winding zero. The proof uses it as a uniform
bound on the inverses; that follows from (6) by the uniform boundedness
principle, and the scaled symbols $`c_w(\rho\,\cdot)`$ satisfy the hypotheses.
Both citations are accurate.

## Exact checks (scripts `finite_algebra.py`, `stability.py`, `exact_small.py`)

- Proposition 2.1: the identity
  $`\det(wI-T_{2m+1}(a))=w\det(H-tU)\,M(t)`$, $`t=w^2-1`$, holds to relative
  error below $`10^{-40}`$ for random complex $`w`$ and perturbed symbols with
  positive and negative powers, $`m\le10`$. The base symbol gives $`H=I`$ and
  $`M(t)=t^m`$ exactly. The Jacobian formula agrees with finite differences
  (relative error $`2\cdot10^{-14}`$, limited by the difference step). The base
  Jacobian $`J^0_{kq}=-2(k+1)\binom{1/2}{m-q-1-k}`$ is exact. The bound
  $`\|H-I\|\le2\sqrt2\,\eta+\eta^2`$ holds on random perturbations.
- Lemma 3.2 identity
  $`\sum_{d=0}^k\binom{1/2}{d+j}\binom{-1/2}{k-d}=\frac{k+1/2}{k+j}\binom{-1/2}{k}\binom{-1/2}{j-1}`$:
  error $`7\cdot10^{-43}`$ for $`k,j<12`$.
- The Gohberg–Semencul formula as displayed in Proposition 2.7: error
  $`4\cdot10^{-16}`$ on a random $`12\times12`$ Toeplitz matrix.
- Tail identity $`\sum_{l\ge t}c_l=\binom{2t-2}{t-1}/4^{t-1}`$ used in the Bezout
  lemma: holds up to the truncation tail.
- End to end at $`m=32`$, $`h=2`$, in 60-digit arithmetic: with the positive
  packet $`10^{-3}s(1+s)`$ the uncorrected $`\det(I-T_{65})`$ is nonzero; after
  solving the two jet equations in the twelve corner coefficients the matrix has
  $`\pm1`$ as double eigenvalues (to $`10^{-29}`$) and
  $`\det(wI-T)/(w-1)^2`$ has a finite nonzero limit, so $`(w^2-1)^2`$ divides
  the characteristic polynomial exactly.

## Numerical checks of the central analytic estimates

All runs use $`h=m/16`$ jets, $`q=3m/8`$ unknowns, $`H^{-1/4}`$ weights and the
normalized Riemann map of the interior of $`h(\mathbb T)`$ computed by the
paper's own Hilbert-transform fixed point (converged to $`10^{-17}`$).

- **Forcing (Proposition 5.4).** For backgrounds vanishing at $`s=-1`$, the
  largest conformal jet times $`m^{3/2}`$ is flat in $`m`$ (positive packet:
  $`6.5\cdot10^{-4}\to6.8\cdot10^{-4}`$; negative packet:
  $`3.2\cdot10^{-5}\to3.1\cdot10^{-5}`$, $`m=128`$ to $`2048`$), and the
  $`H^{-1/4}`$ norm of the first $`h`$ jets times $`m^{5/4}`$ converges. For a
  negative background the jets behave like $`(k+1)m^{-5/2}`$, as the
  first-order formula $`[t^k]M\approx-(k+1)\varepsilon_{m-k}`$ predicts. For a
  negative background that does **not** vanish at $`-1`$ the jets grow like
  $`(k+1)m^{-3/2}`$ and the stage budgets would fail; the separate endpoint
  restoration is therefore essential and is correctly enforced in the proof.
- **Preconditioned Jacobian (Proposition 4.7 and Lemma 5.6).** Singular
  values of the weighted $`h\times q`$ block in the conformal coordinate stay in
  $`[0.9916,\,1.0027]`$ for the positive packet and in $`[0.9986,\,1.0011]`$ for
  a low-degree negative packet from $`m=128`$ to $`2048`$; a nested two-stage
  background gives the same values. In the $`t`$-coordinate the same blocks
  collapse to $`\sigma_{\min}=0.52`$ at $`m=2048`$, so the conformal coordinate
  is exactly what makes the operator uniformly invertible, as the proof asserts.
  For a fixed high-degree negative wiggle ($`5\cdot10^{-4}(s^{-60}+s^{-61})`$),
  $`\sigma_{\min}`$ decreases while $`h`$ passes the wiggle frequency and then
  levels (0.981, 0.950, 0.929, 0.916 at $`m=512,\dots,8192`$), consistent with
  the plateau dictated by the bi-Lipschitz constants of $`h^{-1}\circ f`$.
  Holding $`\|g_0P_-\|_{\mathcal W^{9/8}}\approx0.06`$ fixed while the degree
  grows (30, 60, 120 with $`m=32\cdot\deg`$) gives
  $`\sigma_{\min}=0.9812,\,0.9811,\,0.9816`$: degree-independent, which is the
  content of the two-level theorem.
- **Pencil stability (Proposition 2.7).** $`\max_{t\in h(\mathbb T)}\|W_m(t)\|`$
  grows like $`0.64\,m`$ against the claimed $`C(m+1)^4`$; the weighted norm with
  $`r=1.05`$ stays near 21 for $`m=64`$ to $`1024`$.
- **Completion (Proposition 5.7).** Real solutions of the exact jet equations
  were found at every tested order with residual below $`10^{-18}`$ and
  $`\|x\|_{H^{-1/4}}\,m^{5/4}\approx3.8\cdot10^{-4}`$, matching the forcing norm
  times a unit inverse; the stage-2 solve on the nested background behaves
  identically.

## Logical audit (read, not recomputed)

Checked and found coherent: the even–odd block form and Schur complement; the
coordinate-change lemma; the corner-feedback support argument ($`E^2=0`$ needs
$`q\le(m+1)/2`$, satisfied by $`3m/8`$); the Wiener–Hopf factor and first
inverse row; the exact corner identity and its $`b=0`$ specialization; the
far-factor collar and the winding count $`2p`$; the parity descent to
$`A_t,B_t`$; the Gohberg–Semencul route to $`\|V_N\|\le CN^2`$; the replacement
bound; the Cauchy-integral form of the limiting Jacobian, which reduces to
$`J^0`$ at the base and to the explicit formula when $`P_+=0`$; the restoration
lemmas (packet invisibility, $`D(-1)=0`$, Wiener norm $`1/(k+1)`$ per basis
correction, the $`m^{-1/4}`$ packet bound, the $`n^{-5/2}`$ tail); the endpoint
Schur test; the Wiener divided-difference Cauchy-projection lemma including the
positive-frequency smoothing block; the Bezout kernel bound $`n\log n`$; both
algebraic forms of the unsquared divided difference (rearrangements verified by
hand); the logarithm identity for far factors and the one-extra-derivative
coefficient count; the factorization of the bare operator into isomorphisms and
the treatment of the $`A`$ and $`B`$ parts; the oversampling lemma; the
contraction argument; the selection rule; invisibility of later stages to each
selected section; both Fourier-root limsups; the distance $`\sqrt2-1`$ of $`\pm1`$
from the base range; and the final test-function computation. The budget
arithmetic ($`\beta_j`$ sums, $`\tau_j`$ decay, $`m_0`$) is consistent.

## Limits of this review

1. The explicit constant ledger (Corollary 5.5: $`2^{100}`$, $`\theta_0=2^{-20}`$)
   was not recomputed. The margins ($`\gamma=2^{-1000}`$, $`\theta=2^{-10000}`$)
   are far larger than any plausible error in it.
2. Proposition 4.7 (two-level isomorphism) and Proposition 4.6 (far-factor
   spectral derivatives) were audited for logical coherence and their
   conclusions confirmed numerically; they were not re-proved line by line.
3. Widom's original 1990 formulation was not read. Three secondary sources
   agree with the restatement recorded on the canonical page.

## Minor presentational points

- BFGM (6) is strong convergence; a sentence noting the uniform-boundedness
  step would make the citation exact.
- Corollary 2.8 mentions "m/4 target jets" while the theorem uses
  $`\theta m`$; harmless.

## Recommended canonical summary

Clemens Thalhammer's standalone argument constructs a continuous symbol with
neither one-sided annular extension whose Toeplitz sections carry $`\pm1`$ as
eigenvalues of positive asymptotic proportion along a subsequence, off the
symbol range. This refutes the displayed universal statement of SP-14. The
review found no error; it is an informal AI-agent audit with the limits above,
not human peer review or formal verification. Status **Solved** (negative) is
supported under the repository's definitions, with the original ID, statement
and earlier partial results retained.
