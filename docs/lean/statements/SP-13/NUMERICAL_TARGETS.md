# SP-13 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root`, 2026-09-28. Preimplementation specification; independent approval is required before Lean implementation.

Permanent ID `SP-13`; canonical path `eigenvalues-and-inverse-problems/SP-13/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The complete canonical README is preserved byte-for-byte in `ORIGINAL.md` (SHA-256 `3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a`). Canonical status, author credit and original mathematical target are unchanged.

## Exact target

For every sequence H_n of complex n-by-n Hermitian matrices, every sequence E_n of arbitrary complex n-by-n matrices, and every measurable real symbol f on the closed unit interval, assume H has the specified limiting spectral distribution f and the full nuclear norm of E_n divided by n tends to zero. Conclude the same limiting spectral distribution for H_n+E_n. There are no uniform spectral bounds, normality assumptions on E or H+E, rate of convergence, or individual-eigenvalue matching requirements.

## Concrete mathematical definitions

Use a dependent sequence `A : (n : Nat) -> Matrix (Fin n) (Fin n) Complex`. The irrelevant n=0 term may be included: a limit at infinity does not depend on a finite initial segment, and the 0-by-0 Hermitian requirement is tautological.

Hermitian means entrywise A_ij=conj(A_ji). The nuclear norm is the sum of the n singular values of the actual matrix map between complex Euclidean spaces, using `Matrix.toEuclideanLin` and `LinearMap.singularValues`. The normalized norm is a real quantity. On E=0 it is zero, and no positivity/invertibility promise is added.

The empirical spectral functional at n is `(1/(n:Complex)) * sum_{z in A.charpoly.roots} F(z)`, where roots are a **multiset with algebraic multiplicities**, not a set of distinct roots. A complex n-by-n characteristic polynomial is monic, degree n and splits over Complex, so its roots multiset has exactly n elements, including repeated zeros. Reuse the pinned characteristic-polynomial/roots API only after inspecting these conventions. The value at n=0 is irrelevant.

A test function is any `F : Complex -> Complex` with `Continuous F` and `HasCompactSupport F`. It need not be real-valued, nonnegative, Lipschitz, polynomial, supported on the real axis, or differentiable. The spectral-distribution predicate universally quantifies these functions and requires `Filter.Tendsto` of the empirical complex functional along `atTop` to the complex Bochner integral of F composed with the real symbol embedded in Complex.

Use `f : Real -> Real` with `AEMeasurable f (volume.restrict (Set.Icc 0 1))`, and integrate `F (f(t):Complex)` against that restricted Lebesgue measure. This includes every Lebesgue-measurable interval symbol, including changes on null sets; imposing Borel measurability on the original symbol would be unnecessarily restrictive. The values outside the interval are unused and unconstrained. Conversely such an a.e.-measurable function has a measurable representative on the restricted measure space; changing to that representative leaves every displayed integral and the distribution predicate unchanged. This is exactly the original measurable-symbol target up to its irrelevant a.e. representative. Endpoints are measure zero. No boundedness or integrability of f itself is assumed: F is bounded by its compact support, so its composition is integrable on the finite-measure interval.

The target quantifier order is forall H,E,f, a.e.-measurable f on the interval -> (forall n,Hermitian H_n) -> Distributed(H,f) -> Tendsto(nuclear(E_n)/n,0) -> Distributed(H+E,f). The same f occurs in premise and conclusion; all test functions are quantified separately inside each distribution predicate.

## Review checks and computation

Independently inspect algebraic root multiplicity, actual complex Euclidean singular values, all complex compact-support tests, interval-domain measurability and both limits. This is a qualitative limiting proposition and needs no matrix truncation, sampled eigenvalues, floating-point computation or numerical certificate. The original full trace-norm condition must not be replaced by the previously known Frobenius-small or uniformly norm-bounded cases.

## Formal verification boundary

The implementation must define a closed `Target : Prop` with concrete mathematical semantics, without assuming Target or proving it by placeholder. All imported mathematical meanings require final independent review. The shared pinned LeanCert package uses kernel trust, with `#assert_statement` and `#assert_trust kernel` on Target. Frozen-boundary Comparator identity checks establish correspondence only; they do not prove the problem. No numerical computation is needed merely to state this universal target.
