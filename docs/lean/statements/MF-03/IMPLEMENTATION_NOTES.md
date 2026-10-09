# MF-03 implementation correspondence

Lean implementation author: OpenAI Codex AI agent /root/statement_design.
Mathematical specification author: OpenAI Codex AI agent /root.
Date: 2026-09-28. The approved specification and canonical source are unchanged.

## Exact coefficient conditions

NormalizedPadeRepresentation uses complex Polynomial values P,Q. NatDegree
bounds both degrees by m; the j=0 coefficient equation forces P(0)=1 and the
explicit normalization is Q.eval 0=1, so neither polynomial is zero in any
admissible representation. There is no degree-zero-polynomial convention issue.

The sum over Finset.range (j+1) is precisely i=0,...,j. Every such i satisfies
i<=j, so natural subtraction j-i is the intended coefficient offset, not a
truncated negative index. Nat.factorial (2*(j-i)), cast to the complex numbers,
is an exact positive integer; complex division forms its exact reciprocal.
The coefficient equation holds for every natural j<=2*m, including both
endpoints. It is the Taylor convolution condition Qf-P=O(z^(2m+1)), not a
numerical approximation of f on the disk.

## Reduced representation and the analytic question

ReducedPadeRepresentation requires the above conditions and IsCoprime P Q.
The pinned generic IsCoprime definition is existence of polynomial Bezout
coefficients a,b with a*P+b*Q=1. In the univariate polynomial ring over the
complex field this is precisely absence of a common nonconstant factor.
Consequently a zero of reduced Q cannot also be a zero of P, so denominator
nonvanishing is exactly the source's no-pole requirement for the reduced
rational function.

Cancelling a common factor from an original normalized pair preserves the
required approximation order because that factor is nonzero at zero and is
therefore a local analytic/formal-series unit. Constant rescaling restores
Q(0)=1. It cannot increase either degree. Conversely every pair with the
stated coefficient conditions represents the same rational approximant:
cross-multiplication has degree at most 2m and zero coefficients through 2m,
so the cross-product difference is zero. These observations are mathematical
correspondence explanations, not unproved target axioms inserted into Lean.

Target includes an explicit existence conjunct at every m>=1. Its universal
conjunct tests every reduced representation at every complex z satisfying
the non-strict norm bound ||z||<=3. The complex norm is ordinary complex
modulus, with real-valued result. It demands Q.eval z!=0 and the exact
non-strict error bound ||1-P.eval z/Q.eval z||<=2. Complex division at zero
cannot satisfy the statement merely through a totalization convention,
because nonzero Q.eval z is required in the same conclusion.

The implementation therefore retains all positive orders, boundary points,
complex evaluation arguments, and the original weak constant. It adds no
finite-order cutoff, real-coefficient restriction, denominator-root-location
hypothesis or strict inequality.

## Pinned imported definitions

Inspected source at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474:

- Mathlib/Algebra/Polynomial/Degree/Defs.lean: degree and natDegree.
- Mathlib/Algebra/Polynomial/Eval/Defs.lean: eval2 and eval, exact finite polynomial evaluation.
- Mathlib/Data/Nat/Factorial/Basic.lean: Nat.factorial.
- Mathlib/RingTheory/Coprime/Basic.lean: IsCoprime, the Bezout predicate.
- Mathlib/Analysis/Complex/Basic.lean: the standard real-valued complex norm API.

## Development evidence and scope

The live source compiled with the pinned Lean 4.33.1 macOS runtime and shared
dependency caches, with no warnings after using the current Degree.Defs
import. The closed-statement and LeanCert kernel-trust assertions passed.
The transitive axiom report is exactly propext, Classical.choice and Quot.sound.

Receipts: /private/tmp/nla-mf03-evidence/result.json and MF03.log.
The frozen Reviewed/MF03.lean source was created after successful compilation.
No target proof, artificial numerical certificate, metadata record, or Linux
sandboxed Comparator claim is included. Independent reviewers must inspect
the live/frozen definitions and their full import closure before registration.
