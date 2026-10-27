# Reproduce the independent source review

Use a Git repository containing exact source commit `181c365dc426875aaa61984c901478b1b7c696e6`, the preproof published base and TR-04 reuse commit `653b8f1641415f4160811648ff3e23889ba2e136`. Install Lean 4.33.1 and the exact ten dependencies from `lean-statements/lake-manifest.json`, with their compiled caches available. The drivers assert compiler identity, pinned dependency revisions, tracked cleanliness, frozen input bytes and all expected outcomes. They never build moving worktree sources.

The portable fallback starts an empty project prefix and compiles **all 87** immutable project sources. Set these arguments to appropriate local paths; use a new build directory and output directory:

```sh
python3 reproduce_sources.py \
  --repo /path/to/OpenProblemsInNLA \
  --reuse-repo /path/to/git-containing-exact-TR04-reuse-commit \
  --lean /path/to/lean-4.33.1/bin/lean \
  --packages /path/to/pinned/.lake/packages \
  --build /private/tmp/re06-independent-empty87 \
  --output /path/to/new-evidence
python3 reproduce_audit.py \
  --repo /path/to/OpenProblemsInNLA \
  --lean /path/to/lean-4.33.1/bin/lean \
  --packages /path/to/pinned/.lake/packages \
  --output /path/to/new-evidence
python3 verify_preservation.py \
  --repo /path/to/OpenProblemsInNLA \
  --output /path/to/new-evidence/PRESERVATION_RESULT.json
```

For this actual run, `reproduce_sources.py` additionally received `--prior-source-result` pointing to this reviewer's earlier fresh 63-source receipt. It required the still-present original source/object tree, verified its compiler, pins, source/object hashes and exact 57-input intersection, and copied only those matching objects into a new tree. It then compiled the other 30 inputs. This is an optional optimization for the actual own prefix, not an instruction to trust somebody else's objects. The exact argv, private paths and raw logs are retained in `SOURCE_RESULT.json`; the earlier source receipt, driver and 57 original raw logs are copied into `reused-prefix-evidence`.

The audit compiles its own six exact public signature consumers, live/reviewed identity and reviewed Target consumer, then checks all proof-source constants' actual declaration kinds, kernel trust and transitive axioms. Its 14 negative commands must exit one at the intended error phase. `pass: true` means these expected rejections occurred. No Linux or Comparator execution is performed by these drivers.
