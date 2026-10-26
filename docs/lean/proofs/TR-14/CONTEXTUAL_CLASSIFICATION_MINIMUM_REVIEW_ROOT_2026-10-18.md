# TR-14 other-author source review by /root

Reviewer: `/root`, OpenAI Codex AI agent. Date: 2026-10-18.
Verdict: **approve the named support modules**. No complete TR-14 proof is claimed.

I read the thirteen modules below in full and replayed their actual import
closure in a fresh isolated output directory, without campaign NLA objects.
The retained audit has 16 actual source files plus its generated consumer,
17 successful Lean commands, 65 named declaration checks and 60 theorem-kind
checks. All use Lean 4.33.1, the pinned Mathlib/LeanCert revisions, explicit
LeanCert kernel trust and only propext, Classical.choice and Quot.sound.
Dependency revisions and tracked bytes were checked before and after the audit.
Raw sources, commands, logs and results are in
[verification/root-other-author-review-2026-10-18](verification/root-other-author-review-2026-10-18/).
The reproducible driver is [root-other-author-review-driver.py](verification/root-other-author-review-driver.py).

The mathematical source correspondence was checked against the retained
solution.tex Sections 4–5. The finite-class avoidance proof replaces the
manuscript's Vandermonde-curve selection with a proved finite-subspace argument.

- The stabilizer is the actual algebra of multipliers preserving the actual
  Mathlib product span. Unit scalings are genuine invertible linear maps.
- The transformation lemma constructs S,T by strict finite-dimension induction.
  Its intersection/sum identity, product containment and unit-spanning case
  are proved, with no Kneser inequality supplied as an assumption.
- Finite scalar spectra and finite proper-subspace avoidance give a spanning
  class of actual units. Every auxiliary subalgebra is proved reduced using
  the Frobenius functional, the all-but-one first projection and annihilation.
- Only reduced subalgebras are counted. Their actual idempotent spans, finite
  ambient idempotent set and Artinian decomposition into scalar residue fields
  establish the needed finiteness, even with ambient nilpotents.
- The primitive indicators arise from an actual complex algebra equivalence.
  Nonzero, orthogonal, idempotent, sum-one and scalar-action identities are proved.
- The ordinary minimum is found below the supplied width. A genuine dependence
  deletes a summand and absorbs the exact reweighting into one existing mode.
  Thus actual rank-one functions are independent and entire mode factors are
  nonzero. Individual factor entries remain unrestricted.

| Module | SHA-256 |
| --- | --- |
| ProductStabilizer | `fbbeb013e7d6872681cdc2598051b0bd178423e37fa8a477bccc4fc26852f98a` |
| UnitSpan | `10ec655e20cee3c33b1023dcfc795c25e96deb2914ea90dba5b55768a9b909b7` |
| UnitScaleProducts | `896d50d33f7d07325789bfc26225c4f06c85900e7fd7a39a64c9e4a8736274ce` |
| LinearTransformation | `3722c9a3f7f80b552391529407abbd673c3dea4c5c8614a41443f9b7890e7ebd` |
| UnitScaleAction | `5cb17bbe1ca52f4c36a306302e5c8fd8c2b0f7f952f068054baa77e89e07c17a` |
| UnitTransformation | `cf9ccb517c96ef8adba56cafd08d73bd933c985e8b63196fdada6b187237eb92` |
| UnitAvoidance | `f2d0fcaea7aa6a1cfab62dc335e09d44de7a0a4cc133dfe031df8019a2dc499e` |
| ContextualReduced | `62d2b125bcaf2db2a8d09d3b0bd713ea9b59c5dba84a62b980a1fb18d6ecfd76` |
| ContextualProductStep | `5d2928c68fa47ae093c40ba142fe5fada6f32e5ae6fea470c69a98abb4f706da` |
| ContextualProduct | `a29b46a097cf27117798fd11415f7af269aa84cdaaad6cd8010bfed341ed0ea2` |
| ReducedSubalgebras | `8c5e789cd451446e05d02fd079b1fb9a0421c8029b2e98d3c9c82eafdd662683` |
| ReducedPrimitiveBlocks | `d80c1acdfe8916ffcfdc7700bd441b701eb596fff4023502af7e42b9b23c96cd` |
| MinimumOrdinary | `3016510412bdbadc0415c375f2606aac09ac801d1d1ecb182a5ce9f77bb5c4b9` |

The historical statement/Infrastructure and WidthBasics prerequisites were
recompiled as dependencies; this report does not offer a new independent
source-authorship approval for them. None of the thirteen listed modules was
authored by this reviewer. Root-authored binary reconstruction, chart upper,
product-span, numerical arithmetic and iteration modules are excluded from
this source review and receive separate independent agent reviews.

These are support results, not an unrestricted ordinary lower bound. The actual
graph normalization, primitive block application, block count and final frozen
Target export still need their own proofs and reviews. This local macOS audit
is distinct from an actual isolated Linux CI/Comparator run and is not human
peer review. The permanent ID, canonical problem and original mathematical
statement were not edited.
