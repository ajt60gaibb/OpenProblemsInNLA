# Read-only reproduction

Use a repository containing archive commit `71511f51452f7f59e5c298cf8513df0df0f71781`, accepted input head `669f3cd681b22882836d081a04652880ce39ba24`, source snapshot `181c365dc426875aaa61984c901478b1b7c696e6`, the two archived executed-merge objects and the retained historical objects. Set `REPO` to an exact clean checkout of the archive commit, and `OUT` to this review directory. These scripts only read the repository and write their result files to `OUT`; they do not run Lean, Comparator, CI or restoration.

```sh
python3 "$OUT/review_closure.py" --repo "$REPO" --output "$OUT"
python3 "$OUT/review_phase_manifests.py" --repo "$REPO" --output "$OUT/PHASE_MANIFEST_RESULT.json"
python3 "$OUT/review_committed_archive.py" --repo "$REPO" --output "$OUT"
```

The prepublication checker/result are retained as historical diagnostics. They require the earlier live HEAD `669f3cd6` and are not current-archive reproduction targets. Current acceptance is in `RESULT.json`, `PHASE_MANIFEST_RESULT.json` and `COMMITTED_ARCHIVE_RESULT.json`.
