# IE-04 complete mathematical source review

Reviewer: `/root`. **Verdict: the complete candidate has a sound mathematical
route and preserves the original target; mechanical and publication acceptance
remain pending.** I read all fourteen implementation modules, the frozen
Definitions and all twenty-one Challenge declarations, and the complete
canonical statement and solution. I did not implement the IE-04 proofs.
This is an AI-assisted source review, not external human peer review or a claim
that the currently failing draft has been Lean verified.

The initial source snapshot is the actual development commit
`f559f33671cf6285bf30f9b9a6fb548d18f61229`. The reviewed final snapshot under
`reviewed/` is `f3c22761166868df60938a27bdb08111dfc90f0d`. I read all four intervening
diagnostic-only changes: the Mathlib asymptotic theorem namespace and redundant
tactic, an entrywise measurable identity and finite supremum simplification,
finite-index ordering and the matching witness trajectory rewrite, and scalar
normalization in the Gaussian density. They change no contract or mathematical
argument. `CHECKS.json` binds every final source and records all twenty-one
literal signature matches. The original canonical Markdown and manuscript are
bound to upstream `d8c38a795876b132c90df8d1be8682d3dcde394c`.

## Full problem and probability semantics

The formal proposition retains all dimensions n ≥ 1, every real deterministic
center with actual Euclidean operator norm at most one, every noise scale in
(0,1], every real threshold x ≥ 1, and arbitrary positive real constants c₁,c₂.
The matrix norm is the imported L2 operator norm. In particular, the permitted
counterexample center is the identity, whose norm is proved to be one in
positive dimension; the high-growth matrix is not incorrectly used as the
bounded center.

`gaussianMatrix` is the nested finite product of the n² actual standard Gaussian
measures. The explicit matrix measurable-space instance is the ordinary nested
function-space instance. Probability normalization, exact product rectangles,
the algorithm's measurability and event measurability are separate obligations.
No probability lower bound or Gaussian independence is assumed as a certificate.

The tail event intersects with input nonsingularity. This is sufficient for
the negative canonical conclusion: any total-extension growth-tail event
agreeing with GEPP on nonsingular inputs contains this event, and its proposed
upper bound would also bound this subevent. The proof does not need equality of
these probabilities, a determinant-zero null-set theorem, or an almost-sure
tie assertion. The positive-measure witness box independently proves
nonsingularity and strict pivots everywhere.

`AdmissibleRule` requires validity on every nonsingular input and measurable
growth. Its class is proved nonempty by the actual first-available scan. The
counterexample applies to every such rule, and the final negation explicitly
instantiates that proved rule, so no vacuous rule quantifier is used.

## Actual elimination, maxima and invertibility

The scan compares actual active-column magnitudes and retains the least current
row index among ties. Its connection to `List.argmax` proves maximality and
tie-breaking, including all-zero active columns at the total-function level.
The actual recursive selected trajectory agrees with the separately specified
pivot path. Nonsingular inputs supply nonzero active pivots.

Finite NNReal suprema are connected to attained input maxima and active-entry
upper/lower bounds. The growth numerator includes exactly the n active stages
0,...,n−1, divided by the original input maximum. The latter is proved strictly
positive before every growth division used in the counterexample. Padding
outside an active block does not replace its genuine entries or introduce a
determinant claim about a singular padded stage.

The reused IE-05 generic code is explicitly attributed. I read its full local
source here, including the forward active-block injectivity argument and all
maximal-pivot bounds. Its supported-vector predicate expresses invertibility
of the actual trailing block. The new reverse argument removes the pivot
coordinate, invokes injectivity of the next block, and then uses the nonzero
pivot to recover that coordinate. Backward induction from the empty terminal
block proves original-matrix nonsingularity from actual nonzero pivots. Strict
positive no-swap pivots force every admissible path to coincide by forward
trajectory induction; no path property is assumed for the perturbed box.

## Entire closed-box robustness and growth

The exact witness has the source's triangular nonfinal columns and common
last-column value (3/2)^k at stage k. The symbolic update covers all entries,
all stages, the final scalar block and every n ≥ 2. Its input maximum is one
and its actual peak is (3/2)^(n−1), not merely a lower bound on an unrelated
matrix quantity.

With B=2^(n+2) and δ=2^−(n²+n+1), the exponent identity gives
B^(n−1)δ=1/8. Monotonicity bounds every earlier stage budget by 1/8. The scalar
quotient argument gives p ≥ 7/8, |a| ≤ 5/8, |a/p| ≤ 5/7 and
|a/p+1/2| ≤ 2e. Its divisions explicitly use p>0. The exact error decomposition
then gives e+(5/7)e+2e·2^n ≤ B e for all dimensions concerned.

The trajectory induction uses these inequalities for every matrix in the
closed entrywise box, with no interval samples and no unspecified continuity
radius. It proves the complete active-entry error bound first, then obtains
strict pivoting, path uniqueness and nonsingularity. At the last stage the
diagonal is at least r−1/8, where r=(3/2)^(n−1)≥1. The input maximum is at most
9/8. The strict growth threshold follows since
(r/2)(9/8) < r−1/8 for r≥1. Thus every admissible path exceeds the source's
actual threshold r/2, including every boundary point of the perturbation box.

## Gaussian bound and arbitrary real constants

Only exp(−2)>1/8 is certified numerically. Its explicit
`interval_decide 12 (trust := kernel)` proof was actually accepted with standard
axioms in development run 35027857562. Monotonicity extends it to |z|≤2, and
π<4 gives sqrt(2π)<3, which suffices for the required strict density lower
bound 1/32. The fixed scalar certificate is consumed by the probability proof;
no high-dimensional numerical integration or matrix interval subdivision is
introduced.

Every scalar interval centered within [−1,1] with radius δ≤1/8 lies inside
[−2,2]. The real Gaussian density identity, Lebesgue interval volume, and
nonnegative integral monotonicity give mass at least δ/16. The exact nested
rectangle formula multiplies all n² factors. Symbolic exponent arithmetic
then gives 2^−K, K=n²(n²+n+5). On this rectangle, I+G is in the original
witness box, so measure monotonicity gives the actual all-rule tail lower bound.

For arbitrary real c₁,c₂>0, exponential domination is applied to the real
exponent c₁+4. The exact identity
(3/2)^n/n^(c₁+4)=3xₙ/n⁴ and the bound K≤3n⁴ permit a dimension with
the ratio greater than max(9/c₂,3). This gives both xₙ≥1 and c₂xₙ>K.
All denominators are positive. Strict real-power monotonicity and the
order-preserving ENNReal conversion yield 2^(−c₂xₙ)<2^(−K), which contradicts
the complete proposed tail upper bound at center I, scale one and threshold xₙ.
No proposed constants are restricted to integers and no finite search for a
large dimension replaces this universal step.

## Remaining gates and scope

All twenty-one signatures match the frozen Challenge literally after whitespace
normalization, each appears once in the implementation, and every exported
target has an explicit kernel trust assertion and printed axiom closure.
The source scan found no implementation proof holes, new axioms, native proofs,
unsafe declarations, imported Challenge or disabled kernel checking.
These source facts do not establish that an uncompiled theorem has passed.

Actual run 35027857562 failed on compiler diagnostics and trust assertions for
those failed declarations. Its all-95-input source/log audit is retained and
must not be presented as complete verification. The repaired complete graph is
being checked in run 35029609317. Successful complete compilation, canonical
Linux Comparator and default-kernel replay, all rejection/sandbox controls,
source-bound published-commit evidence and two independent final referees are
still necessary before changing canonical status or counting this problem.
No local Lean/Lake command was run for this review.

The omitted optional source statements for center zero and the weaker shorthand
2^−3n⁴ do not restrict the complete negative canonical result. Historical
conjecture credit remains with Spielman and Teng. The original IE-04 solution
and formalization credit remain George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, with AI
assistance disclosed and no George email added. Review angles follow the
repository's scoped Tau Ceti adaptation; no official endorsement is claimed.
