# MI-22 complete local proof: handoff for independent final reviews

**All eight approved exports are proved and freshly elaborate.** This is the
implementing agent's completion record, not an independent final verdict or a
Linux verification claim. Two independent final proof reviews and the actual
Linux kernel/Comparator workflow remain required before promotion. No canonical
page, mathematical target, problem ID, status, commit or remote branch changed.

Implementation: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, with
AI assistance by agent `/root/leancert_examples`, 12 September 2026. Matthew J.
Colbrook retains attribution for the original negative resolution and method.
The rational adaptation is disclosed in the frozen source correspondence; its
B is not attributed to Colbrook's printed witness. No email is published.

## Statement gate and immutable boundary

The exact statement freeze is `reviews/statement-freeze.json`, SHA256
`d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756`.
Both independent approvals were read and verified before implementation:

- Referee 1: `13556154d85fefbf81b0171bf7ff9028478b2c15327c67c78f3dc7fd18a4129a`.
- Referee 2: `abc0e176440936638ae20ce0b105bc823b125a3fb7eaeaf13f95ff3e14eda1f7`.

`verification/proof-start.json` records all 27 frozen project hashes, eight
original source hashes, both approval hashes, and the absence of implementation
before the first edit. All mathematical statements, numerical targets, source
correspondence, comparator exports and dependency pins remain byte-identical.
The eight original sources still match the immutable base
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

There is one explicitly authorized **build-registration-only** change among the
27 statement inputs. The exact original `lakefile.toml` was archived at
`verification/lakefile.statement.toml` before appending only
`[[lean_lib]] name = "Solution"`. The root authorization, exact append and
before/after hashes are recorded in `verification/build-registration.json`:

- Original: `69b0f047c2c8753489c89814023bcc846c751fc869ce3f9233ab50097308db9b`.
- Current: `750d9ab9828e30c33cee900858a13da3aa6906cd87f84cb757851866db62f5dd`.

`defaultTargets = ["Challenge"]` is unchanged. The explicit proof-build command
is **`lake build Solution`**. The fresh checker verifies that removing the exact
append recovers the archived original, and that all other 26 files match their
original hashes. Final referees should check that precise registration diff.
Historical statement-stage README/source-correspondence prose remains frozen;
the later publication README must describe the completed stage truthfully.

## Complete mathematical result

`Solution.lean` provides the exact eight Challenge signatures. The universal
predicate retains every positive dimension, complex positive-definite A and B,
real t in the closed interval [0,1], every proper singular-value prefix product,
and equality of the full products. Its final export negates that entire
predicate. No numerical condition, commutativity, root approximation or stronger
admissibility premise was inserted.

The implementation is divided into six proof modules:

- `FunctionalCalculus.lean` proves positivity, congruence and all-real-exponent
  principal spectral semantics of the actual CFC power. Ordinary natural powers
  and their principal roots are connected by Mathlib's real-power composition.
- `Norms.lean` explicitly identifies the frozen Euclidean-map norm with the L2
  matrix norm, proves the general squared-Frobenius and action-coordinate bounds,
  and proves the Hermitian eighth-power norm identity from the C-star norm.
- `SingularValues.lean` proves the actual Mathlib family's nonnegativity,
  descending order, multiplicity-bearing adjoint-composition formula and zero
  extension. Its first-value/norm equality follows from the sorted Hermitian
  eigenfamily, positive Gram matrix and actual adjoint/matrix-map identity. No
  user-supplied spectral list or numerical singular-value estimate is used.
- `Witness.lean` proves exact LDL positivity, all proposed diagonal powers, and
  every principal-power identity. For actual Y=B^(1/8), it proves Y positive
  definite, Y^8=B and the noncommuting identity L Y=N in its original order.
- `ExactData.lean` proves every rational multiplication table by finite complex
  matrix algebra. The addition chain T²,T⁴,T⁸ requires three non-diagonal
  squarings; it then verifies B, AB, only the needed row of N, the trace bound,
  tested coordinate and squared-Frobenius estimate.
- `Proof.lean` proves the unit-vector norm, all assembled numerical conclusions,
  root norm and operator gap, consumes the LeanCert point certificate, and gives
  the counterexample plus full negation. `Solution.lean` exports those exact
  conclusions with fresh kernel assertions and axiom reports.

The original A=diag(256,1/256,1) is preserved. The disclosed adaptation uses the
exact dyadic T and defines B=D T⁸ D. Positivity and the actual root identity give
`‖Y‖₂⁸=‖B‖₂≤Re tr(B)<4⁸`, hence `‖Y‖₂<4`. Exact finite arithmetic proves
`44000<Re(Nv)₀`, `‖v‖₂=1`, and `‖AB‖F²<10500²`. The true action and product norm
bounds then give `11000<‖L‖₂`, while the Frobenius bound gives `‖AB‖₂<10500`.
The first singular value is the actual operator norm, so at dimension three and
t=1/8 the required k=1 prefix inequality fails. The equality-at-n requirement
remains part of the universal definition; the proof need not negate every
conjunct separately to refute it.

The table generator `verification/generate_exact_data.py` reads only the frozen
Fraction reconstruction and emits proof data. Lean independently proves every
emitted equality. `verification/generation-check.json` confirms regeneration is
byte-identical to the freshly checked `ExactData.lean`; the generator is not a
trusted arithmetic oracle or a premise of any theorem.

## LeanCert and trust

The single numerical interval task is `numerical_separation : 10500 < 11000`,
proved by `interval_decide (trust := kernel)`. The retained term invokes
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` on the constant
10500, over the single-point domain [0,0], with upper bound 11000. Its Boolean
check is proved by `of_decide_eq_true (id (Eq.refl true))`. No subdivision,
matrix-root enclosure, native decision axiom or approximate spectral oracle is
involved. `verification/fresh-certificate.log` retains this actual term and the
strict singular-value reversal that explicitly consumes it.

All 17 source `#assert_trust kernel` commands pass, and all 17 actual transitive
axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry`, `admit`, custom axiom, `native_decide`, or import of Challenge
in any solution module. The eight intentional Challenge placeholders remain
isolated for later Comparator use and are not imported by the solution.

The actual environment dependency inspector traversed 195 project declarations
and checked 21 required dependencies, including the actual singular-value APIs,
Gram-map bridge, CFC composition, eighth-power norm identity and retained
LeanCert validity theorem. These are actual proof-term checks, not name matches
in comments. The graph and certificate bodies are retained.

## Reproducible local evidence and remaining gates

The explicit `lake build Solution` passed with 3163 graph jobs. Its retained log
reports cache reuse honestly; it is not a claim to rebuild all dependency sources.
`python3 verification/fresh_check.py` separately passed **11 fresh commands**:
Definitions, FunctionalCalculus, Norms, SingularValues, Witness, ExactData, Proof,
Solution, frozen Challenge, actual dependency inspection and retained-certificate
inspection. The old project object directory was excluded from LEAN_PATH. The
only warnings are the eight intentional Challenge holes. All eight normalized
source signatures match exactly; this local signature comparison does not
replace Linux Comparator.

The source check used macOS arm64 Lean 4.33.1 with pinned compiled dependencies.
All ten dependency checkouts are clean and match their pins, including Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. No package checkout was mutated.
Full commands, exit codes, platform, paths, source/object hashes, raw logs,
input identities, signature audit and dependency/trust reports are under
`verification/`. The proof freeze binds these files and the original sources.

Next gates are two independent final code/semantic reviews, truthful candidate
metadata, actual Linux kernel/Comparator/negative-control execution, independent
operational evidence audit, and publication review. This completion record
claims none of those later gates and performs no status promotion.
