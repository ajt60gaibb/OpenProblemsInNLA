# MF-12 independent source repair addendum

**Approve the four minimal source repairs; the complete mathematical-source
approval extends to these exact new bytes.** This does not claim successful
compilation of the repairs or complete MF-12 verification. The original full
source report and the actual failed run35031607095 remain unchanged.

Reviewer: `/root/next_elimination`, independent of the implementation author.
I compared every changed line with the complete-source snapshot and the actual
Linux errors. `before/`, `after/` and the four diff files retain both versions.
`CHECKS.json` binds all nineteen current project source files, verifies that
the other fifteen files are unchanged, and verifies all 28 exported signatures
and the frozen definitions/numerical boundary again.

- RootLimit adds Mathlib's real-power continuity module. That pinned source
  provides the `Filter.Tendsto.rpow_const` and `rpow` declarations used by the
  existing limit argument. No limit statement or proof strategy changes.
- PowerBounds consistently renames the two local lambda-containing names to
  `hLambdaPow` and `hLambdaOff`, avoiding the reserved lambda token. The scalar
  inequalities, finite matrix cases and references are otherwise identical.
- Gaps adds `Nat.cast_id` to the existing simplification of the exact replicated
  word length. This removes the identity natural cast introduced by the natural
  scalar multiplication; it does not change the integer count or floor.
- JordanEntries explicitly rewrites the false previous-column condition using
  the already proved `hrj` before replacing equal row/column values. This is
  the correct diagonal case: the previous-column contribution is zero. It
  does not change Pascal's rule or any endpoint case.

The supplied new hashes match the inspected files exactly. All 28 source
signatures still match the independent Challenge. No model, constant,
quantifier, norm, word order, growth definition or attribution has changed.
No Lean/Lake/build command was run locally. The next actual source-bound Linux
run, final axiom and LeanCert results, default-kernel/Comparator replay and
rejection controls remain pending; whole-problem-verified stays false.
