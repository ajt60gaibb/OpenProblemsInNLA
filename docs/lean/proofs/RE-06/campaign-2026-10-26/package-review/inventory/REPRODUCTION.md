This independent candidate-package review binds corrected commit `0c6d346763a932eb2d379f555e66d8ab3dbf3255`, full proof source `181c365dc426875aaa61984c901478b1b7c696e6`, and package lock `7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153`. It does not claim the separate full-source mathematical reviews, isolated Comparator CLI or actual Linux receipt.

From this review directory, run the static audit in a new output directory:

```bash
python3 audit_package.py --repo /absolute/repository --commit 0c6d346763a932eb2d379f555e66d8ab3dbf3255 --expected-lock-sha256 7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153 --reuse-repo /absolute/TR04-reuse-checkout --output /absolute/new-static-audit
```

The optional `--twin /absolute/candidate-directory` also checks every filesystem byte against the immutable Git package. The reuse checkout must contain the frozen historical commit `653b8f1641415f4160811648ff3e23889ba2e136`; the main checkout must contain the pinned full source, original published base, preproof and authorization commits. The driver reads Git blobs rather than mutable working-tree sources.

Run the fresh 91-runtime source replay, eight independent exact consumers and three real negative compiler commands:

```bash
python3 reproduce.py --repo /absolute/repository --commit 0c6d346763a932eb2d379f555e66d8ab3dbf3255 --expected-lock-sha256 7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153 --lean /absolute/lean-4.33.1/bin/lean --packages /absolute/pinned-packages --output /absolute/new-replay
```

Keep `InventoryPackageAudit.lean.txt` next to the replay driver. It explicitly consumes all six exact public signatures, the live/frozen Target identity and the reviewed Target using the actual target proof. The driver checks genuine theorem kind, LeanCert kernel trust and standard-only axiom sets for the actual six exports plus eight consumers. It compiles only the declared 91 runtime files; archived reference/review Lean files remain inert. It copies actual supplied controls into separate negative modules and requires six real sorryAx failures, the definition-kind failure and the custom-axiom failure, not arbitrary syntax/import errors.

The runtime is official Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, with the exact ten dependency revisions in the package manifest. The replay reuses those clean pinned library caches and creates empty private project source/object directories. It never borrows author RE-06 objects or claims a fresh dependency rebuild. Exact sources, commands, logs, object hashes and dependency heads/cleanliness before and after are retained; all derived project objects are removed.

For a short focused reference-control check, use `check_reference_control.py` with the same `--repo`, `--commit`, `--lean`, `--packages`, a new `--output` and `--expect-six`. The retained original v1 diagnostic intentionally lacks six valid rejections and is not an accepted receipt. Its original script is retained under `diagnostics/check_reference_control_v1.py.txt`.

The actual repository schema validator sources and pinned schema are retained under `metadata-validator/`; run `python3 metadata-validator/tools/lean/validate_manifest.py /absolute/canonical-package` with the repository's locked `jsonschema` and `yaml` dependencies available. The receipt records the actual local invocation and its six-export pass. Generated local Python bytecode was removed and is explicitly listed as regenerable in `REMOVED_REGENERABLE_BYTECODE.json`, never as a required package input.

All paths in recorded commands identify the actual run. Portable parameters allow relocation. Historical v1 rejection and the reviewer-owned initial blank-line comparison diagnostic retain their original bytes and scopes; neither is presented as acceptance.
