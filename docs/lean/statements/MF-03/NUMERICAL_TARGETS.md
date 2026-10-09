# MF-03: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Preimplementation specification; no Lean target has been implemented.

Canonical source: `matrix-functions-and-stability/MF-03/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. SHA-256: `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a`. The complete source is preserved byte for byte in [ORIGINAL.md](ORIGINAL.md), including original target, attribution and history.

## Exact mathematical target and numerical conventions

For every natural order m>=1 the entire series has coefficients a_j=1/(2j)!. A normalized diagonal Pade representation has complex polynomials P,Q of degree at most m, Q(0)=1, and coefficient identities, for every natural j<=2m:

sum over i=0,...,j of Q.coeff(i) / ((2*(j-i))! : complex) = P.coeff(j).

These exact finite coefficient conditions mean Q*f-P has its coefficients through 2m zero. They avoid a branch choice for square root and do not replace the target by a truncated approximation of f on the disk. A reduced representation additionally requires IsCoprime P Q over complex polynomials; Q(0)=1 ensures a nonzero denominator. Degree of the zero polynomial can be handled by natDegree because m>=1 and the coefficient equations in fact force P(0)=1.

Planned target: for each m>=1 (i) at least one reduced normalized diagonal Pade representation P,Q exists, and (ii) every reduced normalized representation at this order has Q.eval(z)!=0 and |1-P.eval(z)/Q.eval(z)|<=2 for every complex z with |z|<=3. The explicit existence conjunct prevents vacuity. The canonical wording already presupposes the approximant exists for each order. Review must confirm that a normalized solution can be reduced while preserving degree bounds, Q(0)=1 and order of approximation, and that the reduced representations determine the same rational function. Since Q(0) is nonzero, cancelling a common factor does preserve the vanishing order. Cross-multiplication and the degree bound show uniqueness: the difference polynomial P1 Q2-P2 Q1 has degree <=2m and vanishes to order >=2m+1, so it is zero. This is a mathematical justification of the chosen representation, not an assumed target axiom.

The denominator condition is imposed on reduced Q. Requiring every unreduced Pade denominator to be nonzero would be stronger and could exclude removable factors, so it is not the target. No assumptions about positive roots, real coefficients, low orders or rational evaluation points are added. The numerator and denominator are complex polynomials, as allowed by the analytic statement; the rational function is fixed by the same Taylor data.

Numerical conventions: order m>=1; complex closed disk norm<=3 (including the boundary); weak error bound <=2; coefficient indices all j from 0 through 2m inclusive; exact factorial reciprocals. No stronger strict inequality for m>=2, sharpness assertion or m<=20 restriction is imposed. No numerical certificate is required just to state the proposition. Future proofs may reduce bounds analytically or use LeanCert kernel certificates but must cover the full disk and every order.

## Review, implementation and scope

The future `NLA.Statements.MF03.Target : Prop` will define the full proposition, without asserting a theorem proving it. Two independent specification approvals must precede implementation. Final independent boundary reviews must inspect all actual definitions and their imported meanings. No target axiom, unimplemented predicate, free semantics or `sorry` is permitted in the proposition.

The existing Solved status and mathematical authorship remain those of the canonical source. This draft claims neither a new proof nor formal verification of the solution. No artificial computation is needed for statement elaboration. The shared LeanCert kernel smoke test is not a proof of this problem.
