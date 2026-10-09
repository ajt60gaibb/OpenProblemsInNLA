Title: TR-13: formalize the complete generic Hankel rank equality

TR-13 has an independently audited informal solution but no existing Lean
project. This PR proves its entire original target in Lean: for every odd
`m ≥ 5` and `n ≥ 2`, a nonempty principal Zariski-open set of complex Hankel
tensors has all five specified ranks equal to `ceil((m(n−1)+1)/2)`.

The upper bound uses a proved Prony recurrence and a determinant/resultant
certificate. The lower bound uses a uniform Koszul witness and determinant
continuity for arbitrary ordinary-border sequences. No part of the original
target is replaced by a conditional theorem or finite-dimensional special case.

The new per-problem project pins Lean 4.33.1 and Mathlib, supplies the independent
Challenge/Solution boundary, full theorem, Comparator configuration, source
hashes, numerical targets, attribution, and scoped review evidence. The
canonical description, resolution archive and generated TeX/PDF link the proof;
all IDs, original targets, status labels and counts are preserved.

Validation completed:

- Full `lake build Solution Challenge` and final theorem axiom audit pass on
  macOS arm64. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the
  target proof; the separate Challenge placeholder is never imported.
- Manifest schema, complete advertised-theorem coverage, source hashes and
  project selection pass.
- All 17 permanent-ID tests and 30 Lean infrastructure tests pass.
- Catalog regeneration and TR-13 math formatting pass. The PDF was regenerated
  and visually inspected.

**Draft:** the canonical Linux sandbox/Comparator run and two fully independent
final reviews remain pending. Existing component reviews disclose each
reviewer's authorship exclusions; they are not presented as whole-project
independent reviews. The problem remains `Solved` pending those gates.

The implementation was generated with OpenAI Codex agents. Matthew J. Colbrook
retains mathematical-resolution credit; Jiawang Nie and Ke Ye retain conjecture
and prior-result credit. No human or source-author endorsement is claimed.
