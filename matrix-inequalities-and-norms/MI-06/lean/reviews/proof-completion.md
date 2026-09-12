# MI-06 proof implementation handoff

**Local build PASS, 12 September 2026.** This is the implementation author's
handoff for two independent final proof reviews. It is not an independent
review, external human review, Linux Comparator result, or catalog promotion.

Both [statement referee 1](statement-referee-1.md) and
[statement referee 2](statement-referee-2.md) approved the frozen boundary before
implementation began. Definitions, Challenge and NUMERICAL_TARGETS remain
byte-for-byte unchanged. Solution's six theorem signatures are copied verbatim
from the Challenge; the Challenge is never imported by Proof or Solution.

## Implemented argument

1. `modulus_eq_sqrt_proved` uses genuine `CFC.abs` and its positivity theorem.
   The generic positive-root helper applies Mathlib's `CFC.sqrt_unique` to a
   proved PSD root and its square identity. Each of the six witness moduli is
   then certified by an exact positive outer-product/diagonal decomposition and
   its actual conjugate-transpose Gram square. All three averages and both
   rank-one decompositions are derived from these actual CFC values.
2. `two_vector_orthogonal_proved` constructs the complex-linear map from
   `Fin 3 → ℂ` to `Fin 2 → ℂ` given by the two conjugate dot products. Injectivity
   would force the false finite-rank inequality `3 ≤ 2`. A nonzero difference
   of equal-image vectors lies in the kernel; positivity of its explicit sum of
   complex norm squares excludes the zero vector. Neither independence of the
   two constraints nor normalization is assumed.
3. Generic quadratic-form lemmas use the real part of the actual complex
   Hermitian form. PSD nonnegativity comes directly from
   `Matrix.PosSemidef.dotProduct_mulVec_nonneg`, and monotonicity uses the actual
   `Matrix.le_iff`. Genuine unitary conjugation preserves the identity and
   carries `u u*` to `(Uu)(Uu)*`. The rank-one terms vanish for the kernel vector;
   the two subtracted conjugated projectors are PSD. This proves the two upper
   bounds of `1/8` times squared length. A PSD diagonal remainder proves the
   lower bound of `3/8` times squared length for the actual sum modulus.
4. The sole LeanCert point statement is `2 < 9/4`, explicitly checked with
   `interval_decide (trust := kernel)` and global kernel mode. The proof term
   uses `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` at the
   singleton domain `[0,0]`; it does not sample unitary matrices or compute
   matrix square roots/eigenvalues numerically. `Real.sqrt_lt_sqrt` consumes
   that certificate directly, and positive division gives `sqrt 2/4 < 3/8`.
5. For each arbitrary complex unitary pair, an assumed PSD domination contradicts
   the three homogeneous bounds on their common positive-length vector.
   Instantiating the complete original universal conjecture at the admissible
   three-dimensional rational pair proves its negation. The stronger informal
   no-finite-constant theorem remains outside the six exports.

The use of existing Mathlib CFC, PSD, outer-product, unitary and finite-rank APIs
follows the campaign's earlier MI-07/MI-29 package structure. No dependency source
was patched, and the pinned dependency manifest and toolchain are unchanged.
The only Lake configuration change after statement review is the default target
from `Challenge` to the now-complete `Solution`.

## Recorded checks

- `lake build Solution`: exit 0, 3,147 jobs, zero warnings, with the pinned
  local dependency cache. The full [raw build log](proof-build.log) is retained.
- All 46 Proof declarations and six Solution exports contain explicit
  `#assert_trust kernel` and `#print axioms` checks. All 52 printed axiom sets
  are exactly `{propext, Classical.choice, Quot.sound}`. Generated auxiliaries
  are covered transitively. [Axiom inventory](proof-axioms.log).
- [Proof-term inspection](InspectProof.lean) exited zero. It checks each direct
  dependency from the public conjecture negation through the counterexample,
  coefficient gap and square-root bound to the kernel LeanCert certificate,
  and prints the actual final certificate body. The [raw log](proof-inspection.log)
  records all five retained edges and the checked dyadic-point theorem.
- The [check receipt](proof-build-result.json) records exact source hashes,
  verbatim signature agreement, all ten clean dependency pins, and the absence
  of `sorry`, `admit`, custom `axiom`, `native_decide`, and `unsafe` in the
  implementation files. The historical six Challenge placeholders remain
  intentional and excluded from the solution import graph.

These checks ran on macOS arm64 and reused independent copy-on-write local
dependency caches at the recorded pins. They are not a fresh Linux dependency
build, sandbox probe, Comparator execution, or raw-kernel export replay.
Those operational checks and both independent final proof reviews remain
publication gates. No mathematical source change, canonical status change,
commit, or push is authorized by this handoff.

Mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA,
with AI-agent assistance. No George email is included.
