# MI-06 independent final proof referee 1

**Verdict: PASS, 12 September 2026.** No mathematical correction is required.
Reviewer: independent Codex agent `/root/solved_statement_inventory`. The proof
was implemented by `/root/formal_review_standards`; I did not author or edit
its mathematical implementation. This is an independent agent review, not
external human peer review, formal novelty certification, or Linux verification.

I read the complete canonical README, Colbrook's complete standalone source
(including its stronger theorem), the frozen numerical targets, every definition,
all of Proof and Solution, the author's build and axiom evidence, and the actual
Mathlib/LeanCert declarations described below. Both prior statement approvals
remain unchanged. The source base is
`02b807770fca860ef810cc048d6849224b8f93e1`.

## Semantic and mathematical findings

The final export proves **the full negation of the original universal
factor-√2 assertion** for arbitrary complex matrices and complex unitaries.
`DominationConjecture` quantifies over every `n ≥ 1` and every complex `A,B`,
then existentially over genuine `Matrix.unitaryGroup` values. Actual elaboration
uses `Matrix.instPreOrder`, i.e. `(right-left).PosSemidef`. No real-input,
Hermitian, invertibility, selected-unitary, or assumed-root premise narrows that
conjecture. Its instantiation at dimension three is admissible. The stronger
informal no-finite-constant result is explicitly outside the formal scope.

- **Actual square roots:** `matrixModulus` is the actual `CFC.abs`, definitionally
  `CFC.sqrt (Xᴴ * X)`, and positivity follows from Mathlib. The six specialized
  roots are each proved PSD by diagonal or positive outer-product decompositions,
  then squared to the actual conjugate-transpose Gram matrix. `CFC.sqrt_unique`
  identifies each root. No table, positivity claim, or spectral list is assumed.
  All three arithmetic averages and both rank-one decompositions follow from
  those actual CFC values.
- **Arbitrary complex constraints:** `two_vector_orthogonal_proved` constructs
  a genuinely complex-linear map from `ℂ³` to `ℂ²` with coordinates `a* w,b* w`.
  Injectivity would give `3 ≤ 2` by Mathlib's finite-rank inequality. The proof
  extracts a nonzero kernel vector without assuming independent constraints.
  Its `squaredLength` is the sum of complex norm squares, and positivity is
  proved from a nonzero coordinate; the default function sup norm is never used.
- **All-unitary quadratic bounds:** genuine unitary conjugation preserves the
  identity and transports `uu*` to `(Uu)(Uu)*`. On the common kernel vector,
  the rank-one terms vanish, and each remaining subtracted conjugate projector
  is PSD. This yields the two `1/8` upper bounds. The explicit PSD remainder
  `S(A+B)-(3/8)I = (3/8)E₁₁` gives the lower bound. The quadratic form is the real
  part of the actual complex Hermitian form; its monotonicity is derived from
  ordinary matrix PSD order, not used as a replacement definition of that order.
- **Strict contradiction:** the final proof combines those homogeneous bounds
  with positive squared length. It covers every pair of complex unitaries,
  and the exported universal negation invokes that counterexample directly.
  No unitary sampling, eigenvalue approximation, normalization assumption,
  or omitted degenerate case appears.

I independently reran my exact `Fraction` reconstruction of all six PSD-root
certificates and actual Gram squares, the three averages, both decompositions,
the PSD lower-bound remainder, and the rational gap `9/4-2=1/4`. This is useful
cross-check evidence, not the formal proof.

## Kernel trust and independent execution

I created a fresh target prefix and **removed the existing project build prefix
from `LEAN_PATH`**. Definitions, Proof, Solution, and isolated Challenge were
then elaborated sequentially, followed by two independent inspection modules.
All six commands exited zero. Definitions/Proof/Solution produced no warnings;
only the six deliberate Challenge placeholders warned. Proof and Solution
never import Challenge. Their six exported signatures match Challenge verbatim,
including all quantifiers; the Comparator config lists exactly those six names,
no replacement definitions, and only the standard three permitted axioms.

All **52** Proof/Solution axiom reports are exactly
`{propext, Classical.choice, Quot.sound}`, and all explicit kernel trust
assertions passed. The implementation and definitions contain no `sorry`,
`admit`, custom `axiom`, `native_decide`, or `unsafe` declaration. The export
checks cover dependencies and generated auxiliaries transitively.

The separate proof-term inspection checks the actual five-edge dependency chain
from the public conjecture negation to `scalar_squared_gap`. That body invokes
`LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` for the constant
expression `2`, rational upper bound `9/4`, and singleton domain `[0,0]`.
The actual certificate is consumed by the square-root comparison and final
contradiction; it is not an unused demonstration. The proof uses explicit
`trust := kernel` plus global kernel mode. I inspected the checked-bound
correctness theorem and point-certificate construction in the pinned source.

This independent run was on **macOS arm64 with Lean 4.33.1**, reusing dependency
caches. All ten dependency Git HEADs match their manifest pins and have clean
source status; no dependency was patched. LeanCert is pinned to
`621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. This is not a fresh dependency-source
build, Linux sandbox test, Comparator result, or exported-environment kernel replay.
**Authoritative Linux verification remains pending.**

## Adapted referee standards and attribution

I applied the correctness, scope, proof-quality, reuse, and attribution rubrics
of Tau Ceti Review at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to this
repository's canonical target and statement/solution Comparator packaging.
This does not claim official Tau Ceti approval or require a separate Tau Ceti
roadmap contribution.

The package is one coherent complete MI-06 target. Generic CFC, PSD, outer-product,
unitary, and finite-rank facts are reused from Mathlib. Private bridges have
actual consumers; the thin public wrappers serve the approved isolated
Comparator boundary. Exact 3×3 entry checks are small and auditable. The rank-one
and homogeneous argument removes both spectral computation and unit-vector
normalization, leaving a single scalar LeanCert point certificate. The few
explicit wrapper/coercion reductions are transparent from their adjacent
definitions; they do not hide mathematical assumptions. No proof-quality or
scope defect warrants a revision to the frozen mathematical source.

The complete informal mathematical counterexample remains attributed to
**Matthew J. Colbrook**, University of Cambridge. Formalization is credited to
**George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA**, with AI-agent
assistance disclosed. No George email is introduced. Mathematical authorship
has not been reassigned to the formalizer.

## Frozen source and evidence

| File | SHA-256 |
| --- | --- |
| `NLA/MI06/Definitions.lean` | `a89c6604d36aec8ae3428df7663a2dbb6f2f923b13ca5f7746aaf4f424cb29d2` |
| `Challenge.lean` | `7774d76c9e362c0f808ee4c1fec3b5607359048d5af82d0e99f60b74c52326dc` |
| `NUMERICAL_TARGETS.md` | `792aa98aa94d18d7b49e4e4b66edca89881f1e38cf51c3aacfed8525644509a4` |
| `NLA/MI06/Proof.lean` | `3c1fdf9ba68e850d26d1307ce6ac2a1e9a1037aba5645bda10aa68e7c3d44145` |
| `Solution.lean` | `389fac775519a84b79b68811e141df5f466e9818469efca889c550e3110b806a` |
| `lakefile.toml` | `94b9d948fbdcfb7cec4b7ae36dff6c5e0cf2927f215d1b7597634ed19961ee09` |
| `lake-manifest.json` | `ff63846f9c3bc57299e95cff597225fb1d99747ab48dad419f97767359b9b102` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `comparator.json` | `1fe56d984d534e7daa8e8eeaacca0543a8be5404f1dc513bf635afb7e54a5dfc` |

The complete pre/post check records **25 unchanged frozen source, configuration,
review, and author-evidence files**. Canonical README SHA-256 is
`0775b70ff8c7e6228e7a289795584be3455aea4d01d8b5721d5fc338dcae494c`;
complete source TeX is
`ae2092528c425b8572c73b07678a01307ed3029399d091a670f78a4d28304bd6`.
Historical metadata may be updated after this review; any change to the nine
mathematical/configuration files above requires explicit review of that change.

Raw independent evidence is in [proof-referee-1-evidence](proof-referee-1-evidence/).
The reproduction script records all commands, the fresh artifact paths, source
and artifact hashes, platform, and dependency pins. Key receipts are:

- `fresh-checks.json`: `ac2640b7f96dfbada2cca50ceb222c54037c4402d9703a28ee7e7e5598a9f49b`.
- `axiom-audit.json`: `352efe4fe539342682bd10d90b458595dcd137d7b49bb66bea9031e583efebf3`.
- `inspection.log`: `0f3e4e231e789f899f10eb37284d456c1d5ba23193f0ce2b81e679bc521faef6`.
- `semantics.log`: `9db7b02727304f62d047686afe8b2298fc60e6f5e1625b7e45e6555eaca769da`.
- `rational-check.json`: `5c301b1ee3724e814a420b959b85d2ae7b3cf04b7dcd3f8124ce0a09e97adfc6`.
- `evidence-manifest.json`: `b922eab19611da926d8d8120b79f24c8cc504d78405560612b841ee9ee5f4bba`.

This review changed only its own report and diagnostic evidence. It made no
mathematical, canonical-status, configuration, Git commit, or publication change.
