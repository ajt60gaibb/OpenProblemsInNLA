# Verification record — 28 September 2026

The complete theorem `NLA.TR13.generic_rank_equality` compiled locally with
Lean 4.33.1 on macOS arm64. [macos-full.log](macos-full.log) records the exact
toolchain, build, theorem type, exit codes, and transitive axiom report.
The final theorem and both full bounds depend only on:

```text
propext, Classical.choice, Quot.sound
```

There is no `sorryAx`, custom axiom or native-execution axiom in the exported
proof. The sole intended placeholder is in the independently compiled
`Challenge.lean`; it is not imported by the solution. The manifest advertises
only the complete theorem, and Comparator selects that same declaration with
no replaceable definition holes.

[SOURCE_SHA256.json](SOURCE_SHA256.json) records the source bytes used for these
checks, including the frozen comparison boundary and dependency pins, with
the subsequent [Comparator configuration correction](CI_CONFIG_FIX.md) recorded
explicitly. All Lean source hashes remain unchanged by that correction. The
temporary development tree used local dependency symlinks to the exact pinned
Mathlib checkout; no symlink, compiled artifact or dependency checkout is part
of the contribution. The committed manifest uses HTTPS Git dependencies.

Additional retained evidence includes the pre-proof
[boundary build](statement-build.log), [upper audit](upper-macos-axioms.log),
[cross-module audit](cross-module-macos-axioms.log), and the scripts referenced
by those logs. The [review index](../reviews/README.md) explains their scope.

## Pending authoritative verification

No fresh non-root Linux sandbox, raw-kernel exporter/Comparator run, or rejection
control result is claimed for this problem. Run the repository commands in
[the project README](../README.md) or its existing GitHub Actions workflow on
the committed revision, retain the resulting logs, and obtain the outstanding
full independent reviews before proposing `Lean verified` status. The proof
already addresses every mathematical case of the original target; these are
verification and review gates.
