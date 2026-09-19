# Full C11 author proof map

The exact frozen `relative_entropy_finite_hockey_stick` passed actual local
macOS Lean in recovery-114. This document explains the source structure for
independent review. It is an author statement, not an independent approval
or a Linux Comparator result. Root alone ran the serial compiler, with one
thread and a 4096 MiB cap. The source author ran no Lean or Comparator.

The target uses the original definitions: `relEntropy X Y` is the real
trace of `X * (logM X - logM Y)`, `E γ X Y` is the trace of the actual CFC
positive part of `X - γ Y`, and `StrictDensity X` is positive definiteness
and complex trace one. No entropy representation is hidden in a definition.
The unchanged Challenge hash is
`1cacb3aa3088860016b9d121904677d56c6c8e6025de9eeaf262957c2bc0d640`.

## The mathematical chain

1. Existing `IdentityShift` differentiates the actual shifted expression
   `D(X+rI,Y+rI)` using two individual eigenbases and the squared absolute
   unitary overlap entries. `IdentityShiftLimit` proves the scalar error
   bound between zero and `(x-y)^2/(y+r)`. Its finite double sum tends to
   the actual `trR(X-Y)`, using both overlap marginals. No common eigenbasis
   or simple-spectrum hypothesis is used.
2. `IdentityShiftFTC` defines `c11_shiftKernel` as the explicit negative
   derivative double sum. `IdentityShiftImproper` proves its nonnegativity
   and actual integrability on `r>0`, with integral
   `D(X,Y)-trR(X-Y)`. The trace correction remains until density
   normalization; it would be false to discard it for arbitrary PD pairs.
3. `NegativeCount` defines `c11_negativeCount M` as the trace of the CFC of
   the strict indicator `x<0`. On every Hermitian matrix it is the sum of
   those indicators over the actual eigenvalues. `NegativeCountLayerCake`
   proves that integrating this count for `M+rI`, `r>0`, gives
   `tracePos(-M)`, including singular M.
4. `NegativeCountMeasurable` approximates that strict count by continuous
   expressions built from `tracePos`. The approximation is eventually
   exact on each finite spectrum, including zero eigenvalues. Thus the
   full two-parameter shifted pencil count is measurable. It does not
   assume measurable choices of eigenvectors or an invertible pencil.
5. Root's `NegativeWeights` and `NegativeCountCongruence` prove complex
   Hermitian congruence inertia. The negative-coordinate projection is
   injective on the negative subspace, so its complex dimension gives the
   inequality; applying the inverse congruence gives equality. This avoids
   realification and a factor of two, and includes singular matrices.
6. `PencilScalar` integrates the explicit weight
   `w(t)=1/(|t|*(t-1)^2)` against `1_{1+tc<0}` for every `c>-1`, proving
   integrability and value `log(1+c)-c/(1+c)`. Positive, negative and zero c
   are separate proved cases. Both infinite tails use explicit logarithmic
   primitives; no quadrature or discretization occurs.
7. `PencilTraceLogBasic` and `PencilTraceLog` connect that scalar sum with
   the actual shift kernel. They prove `tr(log P)=log(det P)` for PD P,
   trace-log normalization under congruence, and the resolvent trace
   identity. They do not assert the false matrix-log congruence formula.
   Every inverse is justified by a proved unit condition. The normalized
   Hermitian C has `1+C` positive definite, hence each eigenvalue c is >-1.
8. `PencilCountBasic` constructs `S=P^(-1/2)` and proves `Sᴴ P S=1`, even
   in dimension zero where that helper has no `hn` premise. With the root
   inertia theorem, `PencilCount` identifies the t-integral of the shifted
   pencil count with the actual shift kernel for each `r>=0`.
9. `PencilIntegral` proves full product integrability of
   `w(t) * count(X+t(Y-X)+rI)` against `(volume restricted to r>0) × volume`.
   The inner norm integral equals the nonnegative integrable shift kernel.
   Only after this proof does Fubini exchange r and t; the layer-cake
   identity yields the actual full-line positive-part pencil integral
   for `D(X,Y)-trR(X-Y)`.
10. `HockeyStickSubstitution` proves positive homogeneity of `tracePos`,
    and vanishing on the central pencil interval `0<=t<=1` by positive
    semidefiniteness. The exact changes `t=γ/(γ-1)` and `t=-1/(γ-1)` give
    respectively `E γ X Y / γ` and `E γ Y X / γ^2` after their Jacobians.
    `HockeyStickChangeVariables` proves both arbitrary-function substitution
    and integrability equivalences using the pinned one-dimensional
    change-of-variables theorem; no unproved regularity premise is omitted.
11. `RelativeEntropyHockeyStick` splits the already integrable full-line
    function into the two tails. It proves the corrected improper
    hockey-stick formula for arbitrary PD pairs, then uses density trace
    one to remove `trR(X-Y)`. The existing two-sided Loewner hypotheses
    imply an identically zero tail above the supplied R. The proved
    zero-tail truncation and existing finite integrability give the exact
    frozen C11 for every R>=1, including R=1.

C12 is downstream and absent from this import closure. The argument makes
no commutation, eigenvalue simplicity, nonzero commutator, conditioning,
or assumed-identity premise. The only nonconstructive Lean axioms printed
for the final C11 theorem are `propext`, `Classical.choice`, and `Quot.sound`.

## Evidence and review scope

The component handoffs record actual source-matched compile results:
identity-shift 091/092; negative count 095/097; scalar pencil and basic
trace-log 103; remaining trace-log 105; integral components 108; scalar and
matrix substitutions 111; final C11 114. Root's inertia source handoff
separately binds its 100/106 results. `HOCKEY-STICK-HANDOFF.json` contains
the exact final command, receipt hash and log hash. Earlier failed sources
and logs remain bound in `author-amendments`; their outputs were not reused
as successful dependencies.

Exact helper statements were recorded before bodies in the seven
`*-STATEMENTS.md`/`STATEMENT-PLAN.md` files. The retained original Challenge
had two independent statement reviews before implementation. Subsequent
helper reviews and their scope are recorded in the phase handoffs and
root/B manifests; the final substitution pre-body freeze is explicit.
Those statement reviews do not replace the still-required independent
final proof reviews or real Linux Comparator for the complete problem.

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, is credited for the contribution.
Sidney Holden's analytic resolution and the relative-entropy inputs of
Peter E. Frenkel, Christoph Hirche and Marco Tomamichel are retained.
This agent authored the fifteen continuation modules; root authored the
two inertia modules. Existing MI27 and retained MI24 sources preserve their
earlier mathematical and code authorship. Neither author can count as a
wholly independent final MI27 referee. No original-target or completed
Lean-verification count increases merely because C11 passed locally.
