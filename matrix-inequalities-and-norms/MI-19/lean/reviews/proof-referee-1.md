# MI-19 independent proof referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`.
The reviewer did not author the MI-19 definitions or proof; the earlier role
was independent statement review. This is AI-agent review, not human peer review.

**Verdict: approve the complete negative formalization of the original target.**
No mathematical correction is requested. Authoritative Linux Comparator and
final publication metadata/evidence remain separate requirements.

## Fidelity and actual proof path

I reread the complete canonical README and the complete Colbrook `solution.tex`
at upstream revision `5adea969c17391693978ada2674d25bb5c3daeb1`, every local
definition and proof, both Challenge signatures, and their public exports.
I inspected the actual pinned Mathlib complex-order, Gram-positivity and
finite-permutation decomposition definitions and lemmas used by this code.

- The universal statement retains complex Hermitian positive semidefinite
  matrices of all orders `n≥2`, every real `q∈[0,1]`, and every nonempty proper
  subset. The matrix is not assumed entrywise positive or positive definite.
  The concrete real matrix is embedded into the complex field, so it belongs
  to the original complex matrix class.
- The rectangular Gram identity is proved entry by entry in complex arithmetic.
  Mathlib's `posSemidef_conjTranspose_mul_self` then proves the actual complex
  quadratic-form condition and Hermitian symmetry. Neither positivity nor
  an alleged Gram identity is an assumed certificate.
- `inversionCount` counts all pairs `i<j` with `σ(j)<σ(i)` in the original
  four-position order. The six-pair formula is proved from that definition,
  rather than substituted for it. The natural-power convention also preserves
  `0^0=1` in the universal statement.
- The full sum ranges over every permutation. The recursive enumeration uses
  Mathlib's genuine equivalence `Perm(Fin(n+1)) ≃ Fin(n+1) × Perm(Fin n)` and
  its proved finite-universe identity. There is no trusted external table,
  sampled permutation subset, native enumeration, or unproved coverage claim.
- The restricted sum filters the same full permutations by setwise preservation
  and retains the same full-order inversion exponent. The singleton `{1}` in
  zero-based `Fin 4` is the paper's interior singleton `{2}`. It selects six
  permutations; the code does not replace the sum by a product of smaller
  permanents or by an initial-segment formula.
- The actual evaluated complex sums are `335001935775/16384` and
  `167502585675/8192`. Their imaginary parts are proved zero, and their
  difference is proved exactly `−3235575/16384`.
- Mathlib's `ComplexOrder` compares real parts and requires equal imaginary
  parts. The strict inequality follows by transporting the LeanCert-proved
  negative real scalar through `Complex.real_lt_real`, then using the proved
  complex difference. Incomparability of complex numbers is not the source
  of the violation.
- All scalar and subset hypotheses are discharged at the concrete witness.
  The strict full-less-than-restricted inequality contradicts the universal
  conjecture's opposite weak inequality directly. Thus `not_subsetConjecture`
  settles the complete original yes/no question negatively. The optional
  positive-definite perturbation and exact-rank-two assertions in the informal
  source are not claimed formalized and are not needed for this conclusion.

## Independent checks and proof quality

I independently re-elaborated `NLA/MI19/Proof.lean` and `Solution.lean` using
`lake env lean` on the local macOS Lean 4.33.1 environment. Both commands
exited zero. This checked the actual proof source, including the scalar
LeanCert certificate, rather than merely accepting a cached build message.
The five audited internal declarations and both public exports each report
exactly `propext`, `Classical.choice`, and `Quot.sound`; all seven
`#assert_trust kernel` checks passed. The [raw outputs and command record](../verification/referee-1/)
state the scope. These are not an authoritative Linux Comparator run.

The proof uses exact algebra and finite sums for the matrix/permutation facts.
The only LeanCert invocation checks the closed rational inequality
`(-3235575:ℝ)/16384<0` in explicit kernel mode. Six increasing index pairs
replace repeated sixteen-pair filtering through a proved identity; the proof
avoids interval subdivision and spectral approximation. The recursive
permutation decomposition and concrete-index lemmas reuse existing Mathlib
facts. The modest recursion-depth setting changes elaboration resources,
not the mathematical statement or allowed axioms.

No custom axiom, native trust, unsafe proof shortcut, hidden hypothesis, or
Solution import of Challenge was found. The two intentional Challenge
placeholders remain in a separate target environment. Public export
signatures manually match the reviewed Challenge signatures; the independent
mechanical Comparator check is still required.

The Tau Ceti correctness, scope, quality, reuse, generality, API, naming,
placement, documentation and attribution angles were applied within this
problem-sized project. Names and local helper placement explain the actual
proof stages; no unnecessary general theory or unrelated result is bundled.
Colbrook retains informal mathematical authorship, while George Stepaniants
receives formalization credit and his approved Caltech department/university
affiliation. No contact email or human-review claim is introduced.

## Frozen reviewed bytes

| File | SHA256 |
|---|---|
| `NLA/MI19/Definitions.lean` | `170e406d1f6bf0ca60e5b65998308b030cf08cc0def51c25c9860524ad3441ac` |
| `Challenge.lean` | `9c838a34cbff20eceb5e842eeca77c310bccb442843925343a7827a1020063cb` |
| `NUMERICAL_TARGETS.md` | `cd93a4cefb529b69755c10bae600718442e0e6b8749c37df87c6dabec9b751aa` |
| `NLA/MI19/Proof.lean` | `53ab38bfef6e52f6c039eba5056659be43f9b8e7a7b3453a62769dc3f0ef3c37` |
| `Solution.lean` | `18bf53ea1d745b4488718297559c3c77e3bcb902596b9c9aae5f448bdcb800c4` |
| `verification/referee-1/check-1.log` | `ca23cbbde93810ca9879964bedfca5f973bdf74e03497ea2c3e17dd41ba8993c` |
| `verification/referee-1/check-2.log` | `ffb04d17d6ccf6a375befddf3537a4034c4a009a6a46f48a54bf6f8c896511fd` |

A substantive change to these mathematical bytes reopens review. The final
README, manifest, Comparator configuration, successful Linux evidence and
immutable proof-source links must be checked before catalog promotion.
