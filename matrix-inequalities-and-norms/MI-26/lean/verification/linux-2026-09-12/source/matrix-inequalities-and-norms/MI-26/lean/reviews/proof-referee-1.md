# MI-26 — independent final proof referee 1

**Verdict: PASS for the complete frozen local formalization.** No mathematical correction is requested. Actual Linux Comparator execution and its operational audit remain pending; this report does not promote the canonical status.

Reviewer: independent agent `solved_statement_inventory`, 12 September 2026. The implementation author was agent `leancert_examples`. I reviewed the statements earlier but did not write or change this project's definitions, challenge or proof. I read the complete canonical problem, complete `solution.tex`, the frozen definitions, all seven challenge statements, numerical targets, complete `Proof.lean` and `Solution.lean`, relevant actual pinned library implementations, and the author's completion/build evidence. I then performed the independent checks below. This is an agent review, not human peer review.

## Frozen boundary and source

The original target and source were inspected at repository revision `587bd896f0e1006f4a4b7f38555e3a523ef85176`. The canonical README SHA-256 is `478e5814b62ebf360cc7a8016a70dc902ac3aa424284c4ce23b528449a72972c`; the complete informal `solution.tex` SHA-256 is `1a26f0d71bf6284d1b5a4c255d48f2318883ded008cd6f778481fe6a8de3bd02`.

| Frozen file | SHA-256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |
| `NLA/MI26/Proof.lean` | `94dd1dde3f1b12002380ae4730ea6396a955f7cbe69a34dde101e7a035fae0af` |
| `Solution.lean` | `a79aa8df0b6b7501dcb6d264fc8a9a21ac0710aa05ed65bff3b244ba97fe6da1` |
| `comparator.json` | `011a5cf15cdf8019f9eed9ac42b9d99a172c114ff7bb36882277a7ba2a510f51` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `59e442a1029185075e33f06e66291c7b4fd9c51582d6792252e763e130d8c26f` |
| `lake-manifest.json` | `9acc9273c38480fe6c996ad47f69580df0049bfdd76f6837866eb809e5893df5` |

The author's proof freeze is `verification/proof-freeze.json`, SHA-256 `327d87623b5e24573bed81eedae77a92b86d09778a4fcded6cebcd069cd8c156`. My before/after checks verified all 38 distinct recorded inputs from the proof freeze, earlier statement freeze, source files and freeze receipts unchanged. The two prior statement approvals remain bound to SHA-256 `c06e27fc583b7abdf6f7c8e7832278f029cf0fefaf937453406faea2eba3a9d7` and `aa91612934d87a6132e3a07636d5c5bef3917366ee3a358690b79e7651fb9a42`.

## Scope and mathematical fidelity

The final theorem proves the negation of the original universal assertion: every positive dimension, all complex positive semidefinite matrices, every real-valued function concave on the nonnegative half-line with only `f 0 ≥ 0`, and existentially chosen genuine complex unitary matrices. The order is Mathlib's positive semidefinite matrix order, verified by the actual elaborated `Matrix.le_iff`; it is not the entrywise order. Conjugation uses actual matrix multiplication and conjugate transpose.

Representing the function by a real extension introduces no regularity restriction. The first export proves equivalence with the ordinary one-parameter concavity inequality, including both endpoints. The generic spectral export identifies actual `cfc (R := ℝ) f A` with the spectral diagonalization for **an arbitrary** real function and Hermitian matrix. I inspected `Matrix.IsHermitian.cfc_eq` and its implementation: continuity on the finite spectrum is obtained in the library and there is no global continuity premise on `f`. The next export proves independence from values below zero using actual nonnegative eigenvalues of a PSD matrix. These are proved bridges, not assumed interpretations of newly defined operations.

For the witness `f(t) = t − t²`, universal concavity follows from the exact identity

`f(θx + (1−θ)y) − θ f(x) − (1−θ) f(y) = θ(1−θ)(x−y)²`.

The proof supplies concavity and `f 0 = 0`; it also records `f 2 = −2`, correctly retaining the wider original function class. A narrower hypothesis requiring global nonnegativity is neither imposed nor refuted. The generic quadratic CFC theorem uses actual `cfc_sub`, `cfc_pow` and `cfc_id'`, with the required continuity supplied for the specific polynomial. Explicit instance inspection confirms that `A ^ 2` is the natural power in `Matrix.semiring`, not entrywise exponentiation.

The two actual complex matrices are

`P = [[1,0],[0,0]]`, `Q = [[9,12],[12,16]] / 25`.

Their PSD properties are proved through complex rank-one outer products, and the idempotence identities are exact matrix computations. Hence their two CFC images are zero. The image of their sum is

`F = [[−18,−12],[−12,0]] / 25`.

For the actual nonzero vector `w = (1,−2)`, the complex quadratic form is exactly `6/5`. For every pair of complex unitaries the purported right-hand side is zero; the matrix inequality would make `−F` PSD and force `−6/5 ≥ 0` through the actual quadratic-form theorem. The proof explicitly consumes the kernel-checked strict scalar certificate to contradict this. Instantiation at dimension two discharges the full universal negation. No numerical witness property, spectral representation, PSD certificate or target inequality is inserted as an extra premise.

The formalization covers the original PSD claim. The informal source's stronger positive-definite extension is outside the exported scope and is not reported as formalized.

## Independent execution and trust

I freshly elaborated definitions, proof, solution, the separate challenge, and three independent inspection modules into a new prefix. The former project output directory was excluded from `LEAN_PATH`. All seven commands returned zero. Definitions/proof/solution emitted no warnings; the separate challenge emitted exactly its seven intended placeholder warnings. The implementation does not import the challenge, and definitions and implemented proofs contain no `sorry`, `admit`, custom axiom, `native_decide` or unsafe proof shortcut.

This was a macOS arm64 execution with Lean **4.33.1** (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). Existing dependency build caches were reused. All ten dependency checkouts were independently checked clean at the manifest's exact revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. I do not claim a clean dependency-source rebuild, Linux execution or Comparator acceptance from these local checks.

The seven public theorem signatures match the seven challenge signatures verbatim, and `comparator.json` requests exactly those seven with empty `definition_names`. Fresh proof/solution output reports exactly 15 audited declarations—eight internal declarations including the scalar certificate, and seven public exports—each with precisely `propext`, `Classical.choice`, and `Quot.sound`. All 15 source `#assert_trust kernel` checks passed. An additional fresh inspection repeats the seven public trust and axiom checks. Auxiliary helper bodies are covered transitively by these dependencies; this count is not a claim of an individual assertion on every auxiliary declaration.

The independent inspection verifies the actual retained dependency chain:

`not_subadditivityConjecture → not_subadditivityConjecture_proved → counterexample_proved → witness_positive`.

The elaborated `witness_positive` body contains `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`, with its boolean check certified by kernel reduction. This is substantive use in the final contradiction, not an unused certificate. The exact rational witness computations are performed by proof-producing algebra; no interval grid or approximate eigensolver is used.

## Referee standards and reuse

I applied the five Tau Ceti rubric themes—correctness, scope, reuse, proof quality, and attribution—at pinned revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, adapted to this repository's canonical-target and trust requirements. This is not a claim of external Tau Ceti acceptance or roadmap admission.

The implementation reuses the actual Mathlib spectral CFC, PSD outer-product/quadratic-form, concavity and polynomial CFC APIs. Bounded library searches and inspected library source hashes are retained. Generic bridges are separated from the small exact witness computations, and the public exports have the independently frozen statements. I found no correctness or maintainability issue requiring revision. The full source mathematical argument remains attributed to Matthew J. Colbrook. George Stepaniants is credited for formalization, with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No George email is included. Existing library authorship is not reassigned.

## Retained independent evidence

All reviewer evidence is in `reviews/proof-referee-1-evidence/`. `fresh-checks.json` records exact commands, elapsed times, platform, output hashes and fresh artifact hashes. `inputs-before.json` and `inputs-after.json` bind all 38 checked inputs; `dependencies.json` records all ten actual clean dependency pins. `source-audit.json` records signature and import checks; `axiom-audit.json` records all 15 fresh reports.

The raw fresh proof and solution logs have SHA-256 `3f26b2753bdce930a95b9970757c8e39395c6f0fa0afc24885244a4da1b0646a` and `835a533c8ae883f8b5aecaf269a7e328ab6c3c676c67f7bc1fca4d4d0d1bd7b3`. The actual dependency/certificate inspection log has SHA-256 `803096dcb3ab0fdd07ee747b08883a666a0d44516bd166dc859048870d42758a`; the semantics and matrix-power inspection logs have SHA-256 `05bf2a783e839a574fba1b67064c49e65b821af4df5a330ee300c69e12f03f6d` and `19d893bc7059417c4f30cad97256a1b7779bf6658c78294cfa8260c506b8f111`.

The independent exact `Fraction` checker reconstructs both outer products, idempotence, the sum/image, the nonzero vector and `6/5` quadratic form. It also independently expands the full multivariate concavity identity as a rational polynomial. Its source and output are retained as supplementary diagnostics, not substitutes for Lean proofs. `library-hashes.json`, `leancert-source-hashes.json`, `rubric-hashes.json` and `reuse-search.log` bind the sources used in this review. `evidence-manifest.json` binds every reviewer evidence file.

**Disposition:** the frozen implementation passes this independent final proof review and is ready for the separate Linux verification stage. No mathematical source, dependency pin, canonical status, commit or publication was changed by this review.
