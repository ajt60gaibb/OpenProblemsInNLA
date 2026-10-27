Run from any repository clone containing source commit d043142e4d7dd45c8a8aee5d10f989f44c356cb9 and metadata commit 21b660e25e313fe6f1d43b57d1338522bf50ea38. Supply the pinned Lean 4.33.1 compiler and manifest dependency cache. Use a new build directory and evidence output, copying these two drivers, consumers.lean.txt, guards.txt and finalize.py there. The source driver refuses an existing build prefix. The audit verifies the source/object/compiler hashes and continuous dependency pins before reusing only this reviewer's newly built prefix. Historical TR-04 snapshots may be relocated with --reuse-repo on the first command.

```sh
python3 reproduce_sources.py --repo "$REPO" --lean "$LEAN" --packages "$PACKAGES" --build "$NEW_BUILD" --output "$NEW_OUTPUT"
python3 reproduce_audit.py --repo "$REPO" --lean "$LEAN" --packages "$PACKAGES" --output "$NEW_OUTPUT"
python3 finalize.py --output "$NEW_OUTPUT"
```

Both actual process phases must pass before finalization. Failed commands remain in raw logs; an unexpected result raises an error. This reproduces local source compilation, exact signature/kind/kernel/axiom audits and seven genuine negative commands. It does not run Linux CI, an exporter, raw-kernel replay or Comparator.
