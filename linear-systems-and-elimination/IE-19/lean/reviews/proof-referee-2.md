# IE-19 independent proof referee 2

Date: 2026-09-12. Reviewer: Codex AI agent `/root/formal_review_standards`.
The reviewer did not write the IE-19 definitions, Challenge, proof or exports.
This is independent AI-agent review, not external human peer review.

**Verdict: approve the mathematical fidelity and proof of the three reviewed
exports, subject to the separately required authoritative Linux Comparator
and publication checks.** This report does not promote the problem to Lean
verified and does not claim that the later sharp-infimum theorem is formalized.

## Scope and adversarial checks

I read the canonical original question, Colbrook's Section 1 counterexample,
`NUMERICAL_TARGETS.md`, every local definition and proof, and the relevant
pinned Mathlib and LeanCert implementation. The source of the original target
is upstream revision `5adea969c17391693978ada2674d25bb5c3daeb1`.

- `Admissible` uses matrix transpose symmetry, strict positivity of every
  entry, entrywise upper bounds by `α I + m 11ᵀ`, and weak diagonal dominance.
  It adds no invertibility, strict-dominance, Loewner-order, or dominance-margin
  premise to the conjectures. All original universal quantifiers and parameter
  restrictions remain in `LowerBoundConjecture` and `SharpConjecture`.
- The chosen dimension is 3 and `α=m=1`; these satisfy the original restrictions.
  The witness has diagonal 2 and off-diagonal 1/2. It is an admissible concrete
  nondegenerate witness, not an empty type or an assumed solution.
- `rowSumNorm` is the finite maximum of nonnegative real absolute row sums,
  coerced to reals. I inspected `Finset.sup`/`sup_const` and Mathlib's
  `Matrix.linfty_opNorm_def`: the expression has the intended infinity operator
  norm meaning. It is not the default entrywise matrix norm. Empty matrices
  have supremum zero, but are excluded by `3 ≤ n` in both conjectures.
- The rational matrices are proved right inverses by exact finite products.
  I inspected the actual `Matrix.isUnit_det_of_right_inverse` and
  `Matrix.inv_eq_right_inv` used to deduce nonsingularity and equality with
  Mathlib's matrix inverse. Totalized inversion of a singular matrix is not
  being exploited.
- Every row of the true witness inverse has absolute sum 7/9, and every row of
  the true comparison inverse has absolute sum 5/4. The proof takes the full
  finite supremum, not a selected entry or a lower/upper estimate of one row.
- The strict inequality refutes the universal lower-bound conjecture directly.
  The full equality-characterized conjecture implies that lower-bound
  conjecture, so its negation is a complete negative answer to the original
  yes/no question. A single valid counterexample is sufficient; this is not
  an attempt to replace a universal affirmative proof by finitely many tests.
- Colbrook's separate all-parameter sharp-infimum replacement is explicitly
  excluded from the formalization's advertised scope. Its mathematical
  authorship is retained; George Stepaniants is credited for formalization.

## Proof structure, reuse and computation

The proof uses existing Mathlib finite-sum, determinant-unit and inverse
uniqueness facts. The short explicit norm definition makes the alternative
matrix norm unambiguous in the auditable statement boundary; it is not a
parallel unproved theory. Names, module placement, explanations and source
attribution are suitable for this problem-sized project. No material reuse,
API, generality, naming, placement or documentation defect was found.

All matrix arithmetic and finite maxima are exact. The only LeanCert goal
is the closed rational inequality `7/9 < 5/4`, with both file-level and
per-invocation kernel mode. It introduces no interval subdivision, transcendental
approximation, artificial parameter search or numerical eigenvalue computation.
This is an appropriately small computation for the requested LeanCert workflow.
I inspected `LeanCert/Tactic/Verification.lean`: kernel trust assertions traverse
axioms and exclude sorry, native-compiler and custom dependencies.

The three exported theorem signatures in `Solution.lean` agree with their
reviewed `Challenge.lean` signatures, using the same definition boundary.
The Solution imports the proved module and does not import Challenge. The
only local `sorry` occurrences are the three deliberate Challenge placeholders.
I found no assumed target, custom axiom, native-decide invocation or unsafe
replacement in the local proof path.

## Checks independently executed

I ran all of the following myself against the recorded bytes:

1. `lake build Solution` — exit 0, 3632 build graph jobs (cached library work
   was reused; this was not a clean-room rebuild).
2. `lake env lean NLA/IE19/Proof.lean` — exit 0, re-elaborating the actual
   proof source, including its LeanCert certificate and trust assertions.
3. `lake env lean Solution.lean` — exit 0, re-elaborating the public exports
   and their trust assertions.

For `strict_scalar_gap`, all three internal proved results and all three
public target exports, `#print axioms` reports exactly:
`propext`, `Classical.choice`, `Quot.sound`. All accompanying
`#assert_trust kernel` checks succeeded. The reviewed source hashes were
unchanged before and after these commands. I also checked all 10 installed
dependency Git revisions against the committed manifest and found no tracked
source changes; the exact results are in `verification/referee-2/dependencies.json`.

The raw independent logs are retained in
[`verification/referee-2/`](../verification/referee-2/); their SHA256 values are:

- `check-1.log`: `420acfdeb8ac5d0dea2cacc4b8cbde99579c381a7e39e482988be5336b4c8b78`
- `check-2.log`: `ac245ba50bb03310248aace6e1850189198ca29b15cb49f125150a92b9636848`
- `check-3.log`: `f5fb8782755aa1029d41b0159bebfa38c18cc1d80f6d71c8cd6631a5d67c789f`

These checks ran on the available macOS Lean 4.33.1 environment. I did not
run the fresh Linux Landrun/Bubblewrap Comparator for this proof, and do not
claim its result. That run must still cover all three selected declarations,
with only the standard three permitted axioms. Metadata, immutable public
links and final source-to-status publication evidence remain separate gates.

## Exact reviewed inputs

| File relative to the Lean project | SHA256 |
|---|---|
| `NLA/IE19/Definitions.lean` | `32dc631cd600154948963a875559cd610d974764fc77f13ab242a573c6dd22b3` |
| `Challenge.lean` | `c79e602bde37c5395eda1376635054776c72c1d803737e1dbfe0a963899627bb` |
| `NLA/IE19/Proof.lean` | `06a534c417911f7db8aca8310699c3862eaf535f8b34ec20b5551218c20a5460` |
| `Solution.lean` | `72fa6092d37c32eb453af0ba83974cc541cb15730080c96dfbaa9226a6f6f658` |
| `NUMERICAL_TARGETS.md` | `71bab6295627b5d68e63a41bfae8a5e82ce11900d334846636f85cf454814c24` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `10d0c9c9dc8b8ac29e372807b94ca53b644aa5c032e6c4b7eb32c90736be66ef` |
| `lake-manifest.json` | `0b2982e346ad245431120cb2eeafa466c9336f1e8bf11525312c0982cb840cb3` |
| `../README.md` | `eea3c53d86f17e4e41a9d1ebcf62454ebd1ac0c296b9305137e44a47bf283488` |
| `../../../references/colbrook-recovered-2026-09-11/manuscripts/IE-19.tex` | `4c50113b3ca261779be36a0058e6b79cb594225098268cd8cc815e6b87b905a4` |

No mathematical source was changed by this referee. A change to any reviewed
mathematical input requires a review update before this verdict applies to it.

## Publication metadata follow-up

I additionally read `comparator.json`, `formalization.yaml` and the project
README after their creation. The configuration selects exactly the three
reviewed public declarations, leaves definition holes empty, and permits only
the standard three axioms. I independently ran the pinned schema/coverage
validator: PASS for all three declarations. The manifest uses the actual
`v0.4` format, distinguishes source authorship from formalization authorship,
records the authorised affiliation without a contact email, excludes the
separate sharp-infimum result, and explicitly leaves Linux verification pending.
The README makes the same limited development-build claim. No publication
metadata finding was identified at these bytes. Pending-review wording may
subsequently be updated to reflect completed reports, but successful Linux
Comparator verification must not be asserted until it occurs.

| Publication file | SHA256 |
|---|---|
| `comparator.json` | `6b02baa6e01466ddde5188c32c90c1063d2ed5163f852b37f0ae776795eec27d` |
| `formalization.yaml` | `7f3b7cdcf904bcb598b6d76497b52181f4361e4f1bae2df88cac42db4eef1ec1` |
| `README.md` | `3e6533ea6a1d3587f8701b3951047a0635940e26e15ebdef957fbb3e6f21a5f8` |
