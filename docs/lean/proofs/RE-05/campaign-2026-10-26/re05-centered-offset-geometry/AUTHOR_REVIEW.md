RE05 centered actual offset and deterministic contraction
========================================================

The two frozen sources contain 17 declarations / 16 theorems in 246 lines.
They use only previously frozen deterministic sources, including actual
regression, custom-fold basis, complement and residual leverage proofs.
They do not import the root Gaussian moment modules under development.
No integral, variance, tail probability or full Target result is claimed.

`CenteredOffset` identifies the literal selected-left measurement inner
product with a rectangular-frame trace, then with the actual selected
projection's Frobenius inner product. The actual frame Gram theorem
discharges the orthonormal-column hypothesis for every actual `makePlan`.
For a residual R with literal Frobenius `inner(E_j,R)=0`, the already proved
selected/residual splitting gives

    selected-left term = -inner(H E_j, H R).

Every actual right summand is exactly the finite quadratic

    g.transpose * A_j * g,    A_j = (H E_j).transpose * (H R).

Its trace is precisely `inner(H E_j,H R)`. Combining those identities with
the actual true-answer rhs gives the unscaled offset identity for every
accuracy parameter. Positive accuracy proves the actual natural Gaussian
width is positive: its ceil argument contains a strictly positive logarithm
term plus a nonnegative threshold/width product. Thus the constant center
can be placed inside the average, proving

    z_j = (1/s) sum_g (g.transpose*A_j*g - trace(A_j)).

Here z_j is the actual original-plan `rhs` on its true residual answers.
The plan is always `makePlan P xi omega copy`; it is never regenerated on
the fold basis. The equivalent entrywise quadratic sum is proved exactly
as `sum_i sum_j A_ij*g_i*g_j`, matching the root moment definition's body.
The two explicit constancy lemmas show the actual H and A_j are unchanged
across all draws and copies for fixed P,xi,R. The residual's orthogonality
is an explicit deterministic hypothesis; the preceding one-copy optimum
block already derives it for the genuine analysis optimum.

`OffsetContraction` first proves that the actual residual-frame columns are
fixed by H, so A_j also equals `(H E_j).transpose*R`. A general finite-family
energy identity expresses the sum of `inner(A_j,A_j)` as

    trace(R.transpose * (sum_j B_j*B_j.transpose) * R), B_j=H E_j.

The frozen exact residual-basis Gram sum identifies the middle matrix with
`H*leverage(P)*H`. The frozen actual residual-leverage Loewner bound says
`threshold*I - H*leverage(P)*H` is PSD. Conjugating by R and taking the
nonnegative trace gives

    sum_j inner(A_j,A_j) <= threshold * inner(R,R).

Trace cyclicity also proves the exact charge bound

    sum_j 2*trace(A_j*A_j.transpose) <= 2*threshold*inner(R,R).

These contraction statements require neither original-generator
independence nor residual orthogonality nor positive accuracy nor a
probability premise. They concern every actual plan and residual matrix.
The A_j may be nonsymmetric. The final sum is exactly the deterministic
quantity used by the general nonsymmetric Gaussian quadratic variance
bound; this module does not itself assert that probabilistic bound.

The development consumer has 22 kernel assertions covering all 17 new
declarations and five literal/boundary checks: actual original-batch rhs
as raw centered quadratic sums, raw variance-charge contraction, actual
width positivity, a dependent zero family and empty-dimensional rhs.
All producers and the final development consumer passed kernel checks with
only the standard three axioms or subsets. Development failures are
retained, including trace-cycle elaboration and consumer alias reduction;
the final preflight is attempt4. Those runs reused project outputs and are
not fresh acceptance evidence. The separate deliberate `sorry` negative
control must fail the final kernel trust assertion.

The source freeze binds every producer, consumer, driver and negative
control, all earlier frozen sources and anchors, and all 18 original/model/
review/registry/pin inputs. It preserves all 217 permanent IDs, originals,
model/Target bytes and status/catalog entries. Fresh replay uses empty
private project outputs, the exact compiler and pinned external package
outputs. This author report makes no independent source-approval, Gaussian
moment/probability/full Target, package, Linux CI, Comparator or promotion claim.
