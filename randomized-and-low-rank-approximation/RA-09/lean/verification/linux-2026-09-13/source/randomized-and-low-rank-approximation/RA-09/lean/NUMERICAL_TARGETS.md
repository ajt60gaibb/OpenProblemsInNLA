# RA-09 numerical and mathematical statement plan

**Statement-only draft. No implementation proof is authorized until two
independent frozen-statement approvals.** The complete source is Colbrook's
`02_frobenius_function_transfer.tex` at upstream
`5830ed4fb06da0659414a3deb2a40ad327aca052`, especially the ordered theorem,
scalar certificate, averaging argument and degenerate cases. The complete
manuscript, including the unneeded unordered theorem and sharpness, was read.

The canonical conclusion is affirmative for every `n≥2`, `1≤k<n`, real
symmetric PSD `Ahat≤A`, continuous nonnegative nondecreasing concave function
on `[0,∞)`, every permitted ordered orthonormal eigenbasis choice, and every
`epsilon≥0`. The premise remains exactly

`FSq A − FSq (truncation dHat k) ≤ (1+epsilon) FSq (A−truncation dA k)`.

The conclusion is the stated relative squared Frobenius error of genuine
`cfc f A` against the function truncation of Ahat. Both truncations use the
same selected eigenvectors. In particular discarded function entries are
zero even when `f(0)>0`. No globally zero-at-zero, operator-monotone, real
analytic, commuting or preferred-basis assumption is allowed.

## Exact universal algebra; no bounded interval computation

The proof route needs no floating-point approximation, interval subdivision,
root search or point certificate. LeanCert will provide explicit kernel trust
and dependency audits. The coordinator approved this pure exact scope. The
unbounded variables in the following scalar certificate must not be replaced
by samples or a bounded box.

For `tau>0`, set `c=f(tau)/tau` and
`h(a)=max(c²a²−f(a)²,0)`. The required ordered scalar inequality, for every
`a,b>0` with `f(tau)>0`, is

`h(a)+2 f(b)f(a)−2c²ba−f(b)²+c²b²`
`≥ f(b) max(f(b)−cb,0) (1−b/a)`.

The scalar consequences of actual concavity/nonnegativity must be proved:
the ratio `f(x)/x` decreases on positive x; `f(x)≥cx` below tau and
`f(x)≤cx` above tau; the stated one-sided Lipschitz bound holds whenever
the larger argument is at least tau. If `f(tau)=0`, the function vanishes
on the entire nonnegative half-line, and this case remains in the final result.

For the branch `b≤tau`, normalize `d=f(b)/(cb)≥1`, `z=a/b>0`. The exact
three certificate factors, on their closed branch endpoints, are

1. `(d−1)/z * [2(d+1)z²−(2d+1)z+d]` for `z≤1`;
2. `(d−z)(2z+d−1)/z` for `1≤z≤d`;
3. `(d−1)(z−d)(2z−1)/z` for `d≤z`.

Use the exact identity

`2(d+1)z²−(2d+1)z+d`
`=2(d−1)(z−1/2)²+(d−1)/2+4(z−3/8)²+7/16`

to prove positivity for every `d≥1` and real z. This avoids discriminant
machinery and any interval arithmetic. The full ordered scalar inequality,
not only these branch polynomials, is a required theorem.

## Actual finite matrix obligations

Define FSq by the finite sum of real entry squares and prove equality both
with `sum |M_ij|²` and the actual Mathlib Frobenius norm squared. Prove its
trace formula, faithfulness and orthogonal invariance. Isolate the Frobenius
norm instance from the genuine CFC instance.

Every actual PSD matrix must admit ordered spectral data; arbitrary chosen
data must give actual orthonormal eigenvectors and the matrix itself. Prove
the CFC formula for every such choice and every scalar function using the
finite actual spectrum, plus independence of the arbitrary extension below
zero. Do not define a proposed spectral sum to be CFC.

For the actual overlap matrix `Q_Aᵀ Q_hat`, use the squared entries as
weights. Prove their column sums are one and restricted row sums at most
one, both actual error expansions and the needed harmonic constraints.
The harmonic lemma follows from genuine PSD of `diag(a)−b vvᵀ`: prove zero
coordinates have zero weight and `b sum(v_i²/a_i)≤1`. Testing the actual
quadratic form at `v_i/a_i` avoids all pseudoinverse foundations; real
division at zero is justified by the separately proved support condition.
Zero selected eigenvalues retain the contribution `f(0)` in the averaging.

The true trace-deficit identity and trace nonnegativity give the residual
bound required by the manuscript. Neither commutation nor a converse
equivalence of the two premises may be assumed. The positive-tail excess
and tail-scaling inequalities then give the exact canonical conclusion.
No best-rank or Eckart–Young theorem is required for that implication.

If the first discarded eigenvalue is zero, the canonical premise must
imply `A=truncation dHat k=Ahat`. For every allowed null-space basis,
the actual transformed error and actual optimal-tail expression both
equal `(n−k) f(0)²`. Do not use `f(0)/0` or assert equality of the differently
selected function truncations.

The unordered factor-two theorem, its optimality, complex extensions and
larger subhomogeneous function class are outside the intended exports.
Matthew J. Colbrook retains mathematical authorship. George Stepaniants
receives AI-assisted formalization credit with Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA, without an email. These are pending proof obligations,
not checked universal claims or a Lean-verified repository status.
