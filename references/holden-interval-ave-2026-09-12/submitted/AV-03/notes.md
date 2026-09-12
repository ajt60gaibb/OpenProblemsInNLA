# AV-03 research notes

## Results worth carrying forward

The main scalar-shooting idea is to parameterize exactly the solutions of the
first n-1 equations by one real coordinate. Global regularity then proves
injectivity of the remaining scalar residual by a secant identity, without
requiring its explicit affine pieces. This gives Theorem H for lower-Hessenberg
matrices and Theorem F for a triangular subsystem with one feedback variable.
Both algorithms recover an exact rational root from a polynomial number of
bisections using a nonzero-coordinate Cramer gap; they do not enumerate signs.

The quantitative residual-recovery lemma applies to arbitrary promised A. It
reduces exact solution to a residual of size 1/(4DG), where log(DG) is polynomial
in input length. The missing part is an unrestricted approximation algorithm
whose cost is polynomial in that logarithmic precision, rather than in D or G.

The exact cyclic handicap formula in `optimized_handicap.md` was obtained while
examining whether positive diagonal rescaling could bound the current
handicap-dependent approach in input length. It proves an exponential
optimized parameter on a fixed-dimensional family, but that family is solved
by the structured algorithm. This is a parameter-analysis result, not a
computational hardness claim.

## Approaches that failed, with preserved obstructions

**Uniform inverse-image separation.** A proposed root-localization strategy
sought a linear functional positive on every (A-diag(d))^-1 r for a fixed
nonzero residual r. The exact four-point convex combination in `result.md`
contains zero. The convex hull of inverse matrices can therefore be singular
although the entire original diagonal family is regular. Two-point intuition
about convex combinations of inverses does not extend to four points.
This does not rule out a separator using additional compatibility between
the current iterate, its signs, and the unknown root.

**Plain sign Newton.** The cyclic family has a genuine three-cycle with all
selected coordinates nonzero for every 0<t<2. Tie-breaking at zero cannot fix
this example. A globalization mechanism requires an independent argument.

**Explicit homotopy tracing.** A simple promised cyclic family has all 2^n
orthants on one straight right-hand-side path, even with determinants uniformly
between 1 and 3. This rules out a polynomial bound on the number of visited
orthants for algorithms that process each such region. It does not rule out
jumping, bisection, or a different method; Theorem H is an explicit example.

**Ordinary Hessenberg reduction.** An orthogonal change of basis generally
turns |x| into a different nonlinear map. Thus the standard linear-algebraic
Hessenberg reduction cannot be applied to an arbitrary A while retaining this
AVE form. No valid general structure reduction was obtained.

**Absence of nonroot stationary points.** The convex hull of limiting branch
gradients of squared residual contains zero only at a root. This does not give
an input-length polynomial convergence bound. The natural quantitative bound
involves the inverse-family constant in value, not merely its bit length.

## Exact transformations checked

The P-LCP equivalence is proved with an explicit positive integer scaling to
avoid the exceptional case M-I singular. No P-LCP instance is discarded by
assuming that inverse exists. Principal-minor positivity is connected to the
AVE promise by columnwise multi-affine determinant interpolation. This is
included for auditing, not claimed as a new equivalence.

## Remaining gaps and productive next directions

The principal gap is replacing the one-dimensional shooting parametrization
by something evaluable in polynomial time for a dense general instance. A
recursive elimination scheme that repeatedly invokes lower-dimensional AVEs
can multiply costs exponentially and is not a solution.

One concrete extension to examine is bounded feedback structure beyond one
free variable. A multidimensional injective residual alone is not a computable
separation oracle, as the inverse-image example warns. A successful extension
needs a genuine additional monotonicity or an efficiently certified cut.

For the existing subclass algorithms, an implementation improvement is to
replace the conservative height and Lipschitz constants by adaptive exact
bounds while preserving worst-case bit complexity. This is secondary to the
unrestricted mathematical gap.

## Reproduction and evidentiary limits

`test_solver.py`, `test_feedback.py`, `verify_obstructions.py`, and
`verify_handicap.py` use exact rational arithmetic. Their finite tests check
implementations and certificates; the all-input statements rest on the
written proofs. No floating-point search result is needed to establish any
claimed theorem. Historical priority of the structured solver theorems and
cyclic handicap formula has not been established by an exhaustive literature
search.
