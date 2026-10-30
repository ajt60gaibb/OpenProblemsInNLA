Use a clone containing immutable closed source commit 05ceb708f444ed36d34afe2eb1f2d98b0b059a0c, the original freeze epochs b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b and de0f0e31d4fc0ff5a09e308dd024b1916311ac7e, and the published base. Supply the pinned Lean4.33.1 binary and ten pinned dependency-cache repositories. Copy the two drivers, two consumers files, guards.txt, finalize.py and the retained AUTHOR_HISTORY_OBSERVATION.json to your new evidence directory. Use a new build prefix; the first command refuses an existing prefix. Historical TR-04 snapshots can be relocated with --reuse-repo on the source command.

```sh
python3 reproduce_sources.py --repo "$REPO" --lean "$LEAN" --packages "$PACKAGES" --build "$NEW_BUILD" --output "$NEW_OUTPUT"
python3 reproduce_audit.py --repo "$REPO" --lean "$LEAN" --packages "$PACKAGES" --output "$NEW_OUTPUT"
python3 finalize.py --output "$NEW_OUTPUT"
```

The audit checks source, own-object and compiler hashes, exact per-scope closure sets and continuous clean dependency pins before and after reusing only the objects just built by this review. It compiles thirteen literal consumers, independent declaration-kind/kernel/axiom checks, and nine actual negative commands. Unexpected outcomes raise an error and leave raw logs. Author-history files are read-only observations retained separately, not extra independent executions. The scripts do not run Linux, an exporter/raw-kernel or Comparator. The common result counts the shared63 source build once.
