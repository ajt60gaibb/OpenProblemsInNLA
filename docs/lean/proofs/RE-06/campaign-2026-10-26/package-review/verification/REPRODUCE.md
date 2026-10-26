# Reproduce the canonical candidate review

The executed independent command was:

```sh
python3 reproduce_package.py \
  --repo /path/to/Git-containing-0c6d346763a932eb2d379f555e66d8ab3dbf3255 \
  --lean /path/to/lean-4.33.1/bin/lean \
  --packages /path/to/exact-pinned/.lake/packages \
  --prior /path/to/re06-full-source-review/verification/SOURCE_RESULT.json \
  --build /private/tmp/new-empty-re06-package-review \
  --output /path/to/new-evidence
```

The prior receipt must be the sealed own-source receipt bound by the adjacent `APPROVAL.json`, and its original private source/object prefix must still exist with identical hashes. The driver enforces this constraint; it never accepts arbitrary author objects. The exact actual private paths, argv and hashes are in `result.json`. The approved full-source review includes the optional wholly fresh 87-source reproduction route; the canonical package itself also includes `reproduce.py`, which compiles all 91 package runtime sources and exercises the three actual controls from an empty project-object prefix.

`ActualComparatorLibrary.lean.txt` is an executed Lean `--run` program using separate imported environments. The driver compiles its four tool modules from the pinned source-lock/archive, then runs six signature comparisons, six actual solution axiom audits and six actual reference-hole rejections. All four tool sources, their lock and the runner are retained here. The driver requires the runner file in its output directory; copy the retained runner to a new evidence directory before reproducing this command.

The metadata validator was separately extracted from the same immutable package commit with both helper modules and the pinned v0.4 schema. Its argv, tool hashes, Python dependency location and successful output are recorded in `METADATA_VALIDATOR_RECEIPT.json`; the actual inputs are retained under `tool-sources/tools/lean` and `tool-sources/docs/lean/schema`.

The package review deliberately does not invoke Docker, the Comparator CLI/exporter, or an external raw-kernel replay. Those are checked by the separately source-bound repository Linux workflow. This local review must not be relabeled as that evidence.
