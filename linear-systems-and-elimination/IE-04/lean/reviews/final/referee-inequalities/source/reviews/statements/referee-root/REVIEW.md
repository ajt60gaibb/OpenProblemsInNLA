# IE-04 independent statement review

Reviewer `/root`, 15 September 2026. Statement author `/root/next_elimination`.

**Approve the complete mathematical boundary, including the explicit standard
product measurable-space instance.** This is a second independent source
approval. Successful Linux elaboration and a source freeze remain required
before proof implementation. I ran no local Lean/Lake commands.

I read the complete canonical README and solution at upstream 8f04b905, the full
Definitions and all 21 Challenge statements, numerical obligations and source
correspondence. CHECKS.json records their exact hashes and immutable source
identities. I inspected the pinned Gaussian distribution/density, finite product
measure and matrix Euclidean operator-norm APIs.

The original quantifiers are intact: arbitrary positive real c1,c2, all n>=1,
all real centers of spectral norm at most one, every 0<sigma<=1, and every real
x>=1. The negative instance uses I_n and sigma=1, with a proved norm-one
identity; W_n is the center of a rare event and is not incorrectly required to
satisfy the deterministic-center norm constraint. Real exponents are used for
the unknown constants.

The explicit GEPP model swaps rows only, uses the actual division-based Schur
update and all n active stages, and normalizes by the actual maximum input
entry. Definitions retain the complete path validity and largest-magnitude
pivot specification. The first-available implementation must be proved to
realize that specification, to be unique among first-available paths and to
supply a measurable admissible rule. Thus the rule class is not silently empty.
The full-box result quantifies over every admissible path, whose equality with
the strict no-swap path is an obligation rather than an assumption.

The probability is the actual nested finite product of n-squared copies of
Mathlib gaussianReal 0 1. That parameter is variance one, as required. Its
definition is ordinary Lebesgue measure with the Gaussian density, with an
IsProbabilityMeasure instance. Measure.pi_pi supplies the product rectangle
identity, but the actual rectangle and event measurability remain explicit
targets. The new measurableSpaceMat alias uses inferInstance at the double
function type and therefore selects the existing product sigma algebra; it
does not replace it with an indiscrete or bespoke measurable space. I inspected
the exact failing compiler diagnostics and the before/after instance edit.
All mathematical data and Challenge bytes are unchanged by that repair.

The tail event intersects with nonsingularity. This is sufficient for a
negative result: it is a subset of any extension of the original GEPP event
on singular inputs, so its strictly excessive probability refutes any proposed
upper bound for that larger event. No equality of probabilities, unproved
Gaussian singular-set nullity or almost-sure pivot uniqueness is needed. The
positive-probability box has strict pivots and is nonsingular throughout.

Every quantitative constant matches the source after changing stage indices to
0,...,n-1. The exponent identity
(n^2+n+1)-(n+2)(n-1)=3 gives B_n^(n-1)*delta_n=1/8.
The perturbed pivot is at least 7/8 and competitors have magnitude at most 5/8.
The quotient bounds 5/7 and 2e give Schur error at most
(2+2^(n+1))*e <= B_n*e. The final pivot and positive input maximum imply growth
at least (8c-1)/9 >= 7c/9 > c/2. These are all-dimension full-box obligations,
not finitely sampled matrix claims. The final stage needs no competitors and
its positive scalar pivot is included in nonsingularity.

For |z|<=2, exp(1)<3 and pi<4 give the actual density greater than 1/27,
hence greater than 1/32. Every scalar interval has length 2delta and lies in
[-2,2], so the lower measure is delta/16. The n-squared product has precisely
exponent K_n=n^2*(n^2+n+5). The final asymptotic declaration must provide an
actual n for every pair of real positive constants, with x_n>=1 and c2*x_n>K_n.
It is not replaced by illustrative rational constants or bounded dimensions.

No blocking scope, vacuity or numerical finding remains in these statements.
The source's optional zero-center claim and shorthand exponent 3n^4 are not
required by the canonical negation and are explicitly unclaimed. Exact scalar
algebra and one fixed density estimate avoid matrix interval subdivision.
The already verified IE-05 generic algorithm definitions are appropriate reuse;
their imported semantics do not supply an IE-04 numerical conclusion.

George Stepaniants retains both solution and formalization credit with his
Caltech Computing and Mathematical Sciences affiliation and no email. Historical
conjecture credit is preserved. This review applies the repository's scoped
Tau Ceti correctness, fidelity, reuse and clarity criteria, not an official
service or human peer review. All 21 proofs, LeanCert assertions, actual
Comparator/kernel/axiom/control evidence and two final independent reviews
remain required after the statement freeze.
