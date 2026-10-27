RE05 deterministic one-copy error bridge
=======================================

Four new frozen sources contain 19 declarations and 17 theorem bodies in
295 lines. They preserve all prior regression7, spectral-split, optimum,
model, original, registry and pin inputs. They prove conditional deterministic
error implications for the literal original algorithm; they do not assert
the probability of the lower/offset events or the full RE05 Target.

`RegressionOffset` is exactly the original `rhs` evaluated on the same
plan's true answers to its matrix argument. Measurement linearity proves
subtraction and its value on a represented matrix. Subtracting a comparison
coefficient vector from the actual normal solution gives

    gram * delta = rhs (true answers to A - represented comparison).

The batch version uses actual `copyResponses` from the original schedule.
In particular it applies to E=orthonormalMember P while keeping precisely
the original `plans P epsilon omega copy`; it never regenerates a plan on E.

`CoefficientError` places coefficient vectors in finite Euclidean space.
If the actual quadratic lower bound is alpha times coefficient norm squared,
and G*delta=z, Cauchy--Schwarz gives

    dot delta delta <= (1/alpha^2) * dot z z.

The proof treats zero coefficient norm separately, cancels its positive norm
otherwise, and divides only by positive alpha squared. The actual-output
specialization uses the proved residual normal equation. No positivity of
an optimum, conditioning oracle or nonzero residual is assumed.

`OneCopyOptimum` proves the exact Frobenius coefficient isometry in the
actual custom-fold basis using the previously derived orthonormality. It
chooses an analysis optimum using only P and A, before any plan or random
draw. Actual supplied-span equality transports the true original Frobenius
minimizer and its residual orthogonality to E. The resulting witness has
actual Frobenius error exactly `optimum P A`, true residual orthogonality to
every E combination, and exact Pythagorean error

    frobenius(A, represent E d)^2 = Opt^2 + dot(d-c*)(d-c*).

This existential optimum is analysis data and is never passed to the
algorithm. No new minimizer or Pythagorean promise is inserted in Target.

`OneCopyError` combines that identity, the coefficient estimate and the
previous conditional equality between the original algorithm's output
matrix and its fixed-plan E-coordinate analysis. It proves actual original
single-copy squared error at most `Opt^2 + (1/alpha^2)*dot z z`. Its bundled
existential endpoint fixes the genuine witness before every plan, alpha
and lower event. For alpha=1/2, the explicit actual offset event
`dot z z <= (xi/4)*Opt^2` gives error squared at most `(1+xi)*Opt^2`.
The actual original-batch version uses its literal copied responses. The
zero-optimum theorem derives exact matrix recovery on the same events,
with no division by Opt. Intermediate lemmas expose their Pythagorean
certificate explicitly; the existential optimum theorem derives it.

All four source bodies and the first development consumer passed LeanCert
kernel checks with only the standard three axioms or subsets. The consumer
has 24 assertions, covering all 19 new declarations and five independent
literal/interface/edge checks: same original actual-plan residual answers,
raw finite-sum Cauchy bound, optimum chosen before all original plans/draws,
actual zero-optimum recovery, and empty coefficient dimension. Development
elaboration attempts are retained and used project objects; they are not
fresh acceptance evidence. The source freeze binds producers, consumer,
negative control, driver, original18 lock and every prior frozen source.

The fresh author replay rebuilds the complete selected ordinary local source
closure from empty private project outputs using exact Lean4.33.1 and pinned
external outputs. Its deliberate `sorry` control must be rejected by the
kernel trust checker. It is a contamination test, not a production theorem.
This report makes no independent source review, Gaussian event probability,
full Target, canonical package, Linux CI, Comparator or status-promotion claim.
