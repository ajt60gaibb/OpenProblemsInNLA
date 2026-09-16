# MF-12 independent statement review

Reviewer `/root`; statement author `/root/next_matrix_functions`; 15 September 2026.

**Approve the complete 28-goal mathematical boundary.** I read the complete
canonical problem page, full attributed manuscript, all Definitions and Challenge
declarations, numerical targets, source correspondence and draft metadata.
CHECKS.json binds the exact files. All three retained source files were compared
byte for byte with Git objects at 8f04b905eb2e0827b6b84f37d9d080ae1f05b202.
This is a source review, not a Lean acceptance or completed formalization.

The final statement covers every nonnegative real exponent, a positive fixed
dimension, two distinct fixed real matrices, positive constants with c <= C,
both inequalities at every positive integer length, and the actual nth-root
limit one. Neither the matrices nor their dimension or constants depend on
length. The norm is the genuine induced Euclidean norm of the Mathlib
continuous linear map. It is not replaced by a maximum-entry norm.

The growth function uses the supremum of every actual allowed list product.
The independent maximum theorem explicitly requires finiteness, nonemptiness,
attainment by an actual list and domination of every list. This rules out
empty-supremum shortcuts, including length zero. The binary-word bridge covers
both choices at every position and does not assume distinctness to code words.
The final construction separately proves distinctness. The chronological
reverse-product convention agrees with the original source.

The six-dimensional matrices and U,V arrays match the source exactly, with
lambda fixed to 1/4 and mu=lambda^(1-alpha) for arbitrary 0 < alpha < 1.
All compressed powers are genuine matrix powers and rectangular products.
The q=0 identities are retained, and the zero-gap real-power identity has
positive exponents on both zero bases. The loss bound and telescoping identity
include arbitrary finite lists, empty lists and repeated zero gaps. For two
successive compressed factors, the earlier gain is multiplied by the later
loss factor, matching the specified tail weights. The finite Holder bound
retains the whole switching list, not a selected reset pattern.

Every binary word has a nonempty list of gaps, including the empty word as
one zero gap. The reset product formula has the correct order and includes
one reset with an empty compressed middle product. For the proposed sufficient
upper constant, each entry of A^r V B U A^s is bounded by
6*2*2*6*H^2*entryMax(B)=144*H^2*entryMax(B). The six-dimensional operator norm
is at most six times the entry maximum. The bound
entryMax(B) <= 1+n^alpha <= 2*n^alpha gives 1728*H^2*n^alpha.
The no-reset powers also satisfy this constant since H >= 1. This enlargement
changes constants only and avoids unnecessary rectangular norm calculations.

For n >= 4, q=Nat.log 4 n gives 4^q <= n < 4^(q+1), q >= 1 and
4^q >= 2(q+1). Therefore k=floor(n/(q+1)) >= n/(2(q+1)) and
k*q*4^(-q) >= q/(2(q+1)) >= 1/4. The prescribed word has exactly n letters,
including its trailing remainder. The Bernoulli obligation implies lost mass
at least 1/5; applying the actual product to V e2 and bounding its norm by two
gives c=(1/4)^alpha/10. This is valid at every n >= 4. At n=1,2,3,
A^n has norm at least one and c*n^alpha <= 1. No subsequence or rounded
logarithm is used. The all-natural Bernoulli statement includes k=0 and ell=0.

The Jordan entries are actual entries of (I+N)^n, not an assumed recurrence.
For n >= m >= 1, each factor (n-j)/(m-j) is at least n/m, giving the stated
binomial lower bound. For 1 <= n < m the diagonal entry one suffices. The
m=0 case has dimension one and lower constant one. The upper bound follows
from the finite sum of binomial coefficients bounded by (m+1)*n^m.
The integer pair {J,0} is distinct and includes every switching word.

The tensor construction uses a specified bijection between Fin(d*e) and the
pair of finite indices. Its entries therefore have maximum equal to the product
of the two entry maxima. The general inequalities
entryMax <= operatorNorm <= dimension*entryMax give precisely the proposed
tensor norm bounds, with positive dimension factors and no assumed SVD theorem.
The actual word identity includes the empty word. The lifted constants
c_alpha*L_m/(6*(m+1)) and 6*(m+1)^2*C_alpha are sufficient for all lengths.
Together with the integer cases, a floor decomposition covers every real
nonnegative exponent without restricting it to rational or computable values.

The root-limit obligation is a genuine convergence statement for the real-power
sequence. Its positive lower bound ensures eventual positivity, and the
standard log/n and constant/n squeeze supplies the required limit. The value
at n=0 is irrelevant. No definition assigns joint spectral radius one without
proving this convergence.

No blocking scope, numerical or vacuity issue was found. The source's extra
dyadic-rational-entry and density corollaries, sharp constants and dimension
optimality are outside the original canonical question and are explicitly
unclaimed by this formalization. Publication must retain that distinction.

The v0.4 metadata schema was actually checked with the available Python venv.
The comparator configuration selects all 28 proposed declarations and no
replaceable definition holes. All 28 Challenge placeholders are deliberate;
Definitions contains no proof holes and no implementation exists. I ran no
local Lean or Lake and no Comparator. Actual successful Linux declaration
elaboration, the second independent approval and an immutable freeze are still
required before proof implementation. Final LeanCert kernel assertions,
Comparator/default-kernel/axiom/control evidence and two independent final
referees remain required before any verified count or publication claim.

Original mathematics remains attributed to Matthew J. Colbrook, University of
Cambridge DAMTP. Formalization is credited to George Stepaniants, Department
of Computing and Mathematical Sciences, California Institute of Technology,
without his email. This review applies scoped Tau Ceti fidelity, correctness,
clarity, attribution and reuse criteria; it is not official service approval
or external human peer review.
