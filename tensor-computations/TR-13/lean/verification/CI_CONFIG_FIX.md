# Comparator configuration correction — 28 September 2026

The first submitted revision, `ea6fe7fdd4804370aa0bf1275c1b6209211bf2eb`,
omitted the required `challenge_module` and `solution_module` entries from
`comparator.json`. The metadata validator passed, but the verification
harness's separate `validate_project` check rejects that configuration with
`HarnessError: unsupported Comparator config keys`.

The [first Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/36417674887)
retained artifact `lean-TR-13` (GitHub artifact ID `10968043855`). Its bootstrap,
sandbox, Comparator regression, and kernel-control logs pass; its negative
axiom fixtures are rejected as required. There is no project dependency or
project Comparator log: the run stopped before the TR-13 proof check.

The configuration now explicitly selects `Challenge` and `Solution`. The
advertised theorem, permitted axioms, empty definition-hole list, all Lean
sources and all dependency pins are unchanged. `SOURCE_SHA256.json` records
the corrected configuration hash; its other 20 entries are unchanged.

Local checks performed after the correction:

- Replayed the original configuration through `tools/lean/harness.py`'s
  `validate_project`: rejected with the error above, as expected.
- Ran `validate_project` on the corrected project: passed.
- Ran `tools/lean/validate_manifest.py`: passed, one complete theorem.
- Verified all 21 entries in `SOURCE_SHA256.json`: passed.
- Ran all 12 `tools/lean/test_harness.py` tests: passed.
- Ran `git diff --check`: passed.

This is a configuration preflight result on macOS, not a substitute for the
canonical Linux sandbox, Comparator, or raw-kernel verification. Those checks
must run on the corrected committed revision in CI.
