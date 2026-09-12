# MI-29 implementation completion record

This is the implementer's handoff, not an independent referee report. The complete five-export proof compiled successfully with `lake build Solution` (3147 jobs, exit 0, no warnings) after both statement referees approved the frozen boundary. Definitions, Challenge and NUMERICAL_TARGETS remain byte-for-byte unchanged. Independent final proof review and authoritative Linux Comparator are subsequent checks coordinated separately.

## Proven scope and analytic bridges

The theorem negates the exact canonical all-dimension complex-matrix statement with positive definite A, invertible Hermitian B, and arbitrary nonnegative real k,p. It does not claim to refute variants requiring B positive definite or restricting k=2. All witness hypotheses are conclusions, not assumptions.

- `spectralPower_natCast`: actual `CFC.rpow` equals the actual matrix ring power for every PSD matrix and natural exponent, including zero, using `CFC.rpow_natCast`.
- `modulus_power_eight`: the actual `CFC.abs` is `CFC.sqrt (X.conjTranspose * X)` by its definition; `CFC.abs_nonneg` and `CFC.abs_sq` establish positivity and the exact eighth-power reduction.
- `comparison_positive_real`: `IsStrictlyPositive.rpow`, the Matrix positive-definite bridge, and `PosDef.add_posSemidef` give positive definite left/right matrices; `PosDef.det_pos` and `Complex.pos_iff` produce positive real determinants. The public statement retains every original hypothesis. The auxiliary proof actually needs fewer of them, because every totalized CFC real power is nonnegative and every real power of positive definite A is positive definite; this strengthens a proved auxiliary fact without changing the conjecture or its counterexample.
- `counterexample`: A=diag(2,1,1/2), B=(1/5)[[-1,2,0],[2,1,2],[0,2,1]], k=6, p=8 is derived to satisfy every admissibility hypothesis. det(B)=-1/125 proves invertibility. Its negative first diagonal entry and positive second diagonal entry establish that neither B nor -B is PSD.
- `not_modulusDeterminantConjecture`: specialize the full universal target at that admissible witness, then contradict its weak comparison with the proved strict reverse inequality.

The exact determinant identities are L=136990346414301954149/61035156250000000000 and R=4537743716162890657/1907348632812500000. Their exact difference is R-L=21036678407451/156250000000000>0. All displayed fractions denote actual complex determinant values with zero imaginary parts.

## Computation and trust

The proof derives the actual Gram identities by Hermitian conjugation and associativity. Each Gram matrix is squared once and that result squared once more. Private finite matrix certificates are checked against actual matrix multiplication by exact `norm_num`; they are not assumed. Matrix.diagonal_pow handles A^6. Only two exact 3x3 determinants are evaluated. No eigenvalue approximation, square-root approximation, general interval subdivision, exhaustive parameter search, or optional polynomial-in-z certificate is used.

One retained LeanCert point theorem, `scalar_gap_positive`, proves the strict rational gap with `interval_decide (trust := kernel)`. The whole proof also sets `leancert.trust` to `kernel`. The minimal `LeanCert.Tactic.IntervalAuto.PointIneq` import is sufficient. `witness_strict_violation` explicitly transports this theorem through the exact complex real-part identity and `sub_pos`; it remains in the target dependency chain.

Ten audited internal theorems and all five Solution exports each pass `#assert_trust kernel`. Every corresponding `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`; `reviews/proof-axioms.log` contains the 15 raw print lines. Proof and Solution contain no `sorry`, `admit`, custom `axiom`, or native execution tactic. The five deliberate Challenge placeholders are in the separate statement target and are never imported by Solution.

## Source and ownership

The mathematical counterexample and informal proof are Matthew J. Colbrook's. Formalization author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. No email is included. Canonical pages and status have not been edited by the implementer. No commit or push has been made by the implementer.

## Frozen source and evidence

`reviews/proof-freeze.json` binds the complete source and dependency configuration plus both prior statement approvals. The proof build command, exit code, timestamps and raw log hash are recorded in `reviews/proof-build-result.json`.

- `NLA/MI29/Definitions.lean`: `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` (3010 bytes).
- `Challenge.lean`: `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` (2430 bytes).
- `NUMERICAL_TARGETS.md`: `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` (12986 bytes).
- `NLA/MI29/Proof.lean`: `b683a2c0faebd595f7d9f2b0973a9955cf39443c924f7dfd05b3b60e16bdadf5` (12381 bytes).
- `Solution.lean`: `0cb66f4fc4d379f1f91699ba16b6feda93710798fe414fa09b242cd12076ce11` (3273 bytes).
- `reviews/proof-build.log`: `72e29309b257a259ad24cbab1f05248bd353b1cbcae177a146b5b842ec3d4b23` (1994 bytes).
- `reviews/proof-axioms.log`: `dd6f6a36fc9f20309f3921c4cb2094d78ab889d3f5e529ae0a3b5614c00cd0a8` (1871 bytes).
