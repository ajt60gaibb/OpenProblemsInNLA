# NLA submission bundle

This archive consolidates all files retained from both research attempts in the conversation. It is a review bundle, not a declaration that an open problem has been resolved.

## Contents

- `AA01_submission/`: the proposed AA-01 proof in PDF and LaTeX, the review/issue draft, and two retained JSON verification logs.
- `NLA_partial_results_submission_package/`: the earlier AC-11 and AC-12 finite-case package, unpacked with its original proofs, data, source code, reproduction scripts, review drafts, and verification logs.
- `retained_originals/`: the original finite-case ZIP and standalone PDF, preserved byte for byte.
- `previews/`: all retained preview images, including intermediate manuscript renders. These are ancillary and are not authoritative mathematical documents.
- `FILE_MANIFEST.json` and `SHA256SUMS`: inventory and integrity hashes for the bundled files.

## Research status and limitations

The AA-01 manuscript is an AI-assisted, unreviewed proposed proof. Its correctness and novelty have not been independently established. It should be submitted for scrutiny, not represented as an accepted solution.

Only five AA-01 files remain available: the PDF, LaTeX source, issue draft, and two JSON logs. Experimental programs and additional logs referred to in the earlier conversation or manuscript were not retained and are NOT present in this bundle. The retained logs alone do not make those experiments reproducible. No missing source files have been reconstructed or invented. The PDF and LaTeX are preserved as received; the earlier delivery indicated that the LaTeX contains verification information added after the PDF was compiled.

The AC-11 and AC-12 contributions are finite-order partial results, not complete resolutions of the universal problems. Their existing package documentation describes their scope and reproduction commands.

Packaging checks cover file presence, byte hashes, and ZIP integrity only. The mathematical arguments and numerical claims were not revalidated during this packaging step. No external submission has been made.

## Preparing a repository contribution

Extract this archive and review `AA01_submission/review/AA-01_issue_draft.md` and the earlier package's review drafts before submitting. Preserve the provisional and partial-result labels. For a clean source-tree contribution, use the unpacked research folders; `retained_originals/` and `previews/` are optional archival duplicates and supporting images.

For the earlier finite-case package, consult its README and run its reproduction script from within that package's directory. There is no complete AA-01 reproduction script in the retained material.

## Integrity verification

From this bundle's root directory, run:

```sh
sha256sum -c SHA256SUMS
```

The checksum file covers every other file in this archive, including the manifest. It does not checksum itself.
