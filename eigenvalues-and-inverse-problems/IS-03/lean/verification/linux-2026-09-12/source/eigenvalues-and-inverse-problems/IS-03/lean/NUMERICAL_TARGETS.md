# IS-03 exact statements before proof

This is the statement-first plan for the complete original negative answer, at upstream `f41f1f9ffa2171550d4bb795862c6170c4f26070`. No proof implementation exists. Two independent approvals must precede the first proof edit.

Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Matthew J. Colbrook retains mathematical authorship of the counterexample. Johnson and Hoover–McCormick–Paparella–Thrall retain the original conjecture/source attribution. No George email is added.

## Full original quantified target

For every natural n≥5 and every real entrywise-nonnegative n×n matrix A, the conjecture asks for a real entrywise-nonnegative (n−1)×(n−1) matrix B whose actual characteristic polynomial equals `(1/n) • derivative(A.charpoly)`. Matrices, determinants and the formal polynomial derivative must be genuine Mathlib operations. Equality is polynomial equality, not equality at sampled points. No symmetry, irreducibility, zero-trace, invertibility, simple-spectrum or diagonalizability assumption may be added. The final export negates this entire universal assertion.

## Exact source witness

Use precisely the real source matrix, with rows

```
[1/2,0,0,0,0,0,0]
[0,0,1,0,0,0,0]
[0,1,0,0,0,0,0]
[0,0,0,0,1,0,0]
[0,0,0,0,0,1,0]
[0,0,0,0,0,0,1]
[0,0,0,1,0,0,0].
```

It must be proved entrywise nonnegative, with trace 1/2. Its actual characteristic polynomial must be proved equal to

`p = (X−1/2)(X²−1)(X⁴−1)`.

Its actual normalized formal derivative must be proved equal to the monic degree-six polynomial

`q = X⁶−(3/7)X⁵−(5/7)X⁴+(2/7)X³−(3/7)X²+(1/7)X+1/7`.

## The essential all-real-matrices bridge

For **every** real 6×6 matrix B with actual `B.charpoly = q`, prove all seven identities

| k | trace(B^k) |
| --- | --- |
| 1 | 3/7 |
| 2 | 79/49 |
| 3 | 48/343 |
| 4 | 6731/2401 |
| 5 | 5213/16807 |
| 6 | 219766/117649 |
| 7 | −8593/823543 |

These values are theorem conclusions, never premises. A computation on one companion matrix is insufficient. Any use of eigenvalues must retain algebraic multiplicities and justify the trace-power identity; diagonalizability must not be assumed. A proved equivalent algebraic characteristic-polynomial-to-trace argument is allowed. The formal boundary uses actual real matrix trace and powers, independently of the proof method.

The exact scalar recurrence is `7s₇=3s₆+5s₅−2s₄+3s₃−s₂−s₁`. Its numerator at denominator 7⁶ is `659298+182455−659638+49392−189679−50421=−8593`.

Prove generically that every natural power of an entrywise-nonnegative real matrix is entrywise nonnegative and has nonnegative trace. This includes power zero and dimension zero; the original conjecture itself retains n≥5. Applying it to a putative nonnegative B contradicts the negative seventh trace. The full order-seven counterexample then refutes the original universal target.

## LeanCert and computation

Plan one materially consumed **kernel LeanCert** singleton certificate for `(-8593/823543 : ℝ) < 0`. The certificate must feed the seventh-trace contradiction and final negation. It certifies only that scalar inequality; every matrix, polynomial, derivative and general trace bridge still requires exact Lean proofs. Avoid approximate roots, numerical eigensolvers, interval subdivision and direct symbolic enumeration of all sixth-order matrices. Use the witness's 1+2+4 block structure and exact polynomial arithmetic.

## Advertised exports and exclusions

The seven reviewed exports will be `nonnegative_power_trace`, `witness_admissible`, `witness_polynomials`, `trace_moment_certificate`, `negative_moment`, `counterexample` and `not_derivativeRealizabilityConjecture` in namespace `NLA.IS03`.

The manuscript's stronger exclusion after arbitrary zero padding, its separate moment-conjecture consequence, smallest-order questions and historical priority are outside the exports. The entire original exact-order yes/no problem remains covered. Only genuine actual Linux Comparator/default-kernel success after two final independent reviews may support a later Lean-verified status.
