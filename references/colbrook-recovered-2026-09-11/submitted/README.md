# Recovered numerical linear algebra results

**Seven proof notes covering eight candidate results, with exact-arithmetic checks and submission-review drafts.** This package was reconstructed from the earlier mathematical record. It is not a bit-for-bit recovery of a previously delivered archive.

Read the [combined manuscript (PDF)](Research_manuscript.pdf), the [combined Markdown manuscript](Research_manuscript.md), or an individual note below. The [status ledger](STATUS.md) distinguishes finite exact checks from analytic proofs. [Recovery and corrections](research/RECOVERY_AND_CORRECTIONS.md) records the reconstruction, the corrected LSMR fraction, missing materials, and AI assistance.

## Contents and status

The IE labels below are **provisional local labels from recovered notes**, not verified current repository identifiers. The formulations printed in the notes define the precise claims.

| Local label | Candidate result | Files | Verification scope |
|---|---|---|---|
| IE-13 | Sharp unequal-bandwidth GEPP growth recurrence | [PDF](proofs/IE-13.pdf) · [Markdown](proofs/IE-13.md) · [LaTeX](proofs/IE-13.tex) | 60 exact attaining constructions; general upper bound is an analytic proof draft |
| IE-14 | Cyclic-tridiagonal growth $F_{n+1}+1$ | [PDF](proofs/IE-14.pdf) · [Markdown](proofs/IE-14.md) · [LaTeX](proofs/IE-14.tex) | Exact constructions for orders 4–30; universal upper bound requires review |
| IE-17 | LSMR spectral backward-error and approximation nonmonotonicity | [PDF](proofs/IE-17.pdf) · [Markdown](proofs/IE-17.md) · [LaTeX](proofs/IE-17.tex) | Exact iterates, rational perturbation, and strict positive-definiteness certificates |
| IE-18 | Failure of a proposed four-step Anderson bound | [PDF](proofs/IE-18.pdf) · [Markdown](proofs/IE-18.md) · [LaTeX](proofs/IE-18.tex) | Exact examples and independent recurrence check; asymptotic convergence is not resolved |
| IE-19 | Entrywise inverse-norm counterexample and sharp infimum | [PDF](proofs/IE-19.pdf) · [Markdown](proofs/IE-19.md) · [LaTeX](proofs/IE-19.tex) | Exact counterexample and parameterized identities; entrywise-order formulation only |
| IE-21 | Random spherical row-deletion limit | [PDF](proofs/IE-21-22.pdf) · [Markdown](proofs/IE-21-22.md) · [LaTeX](proofs/IE-21-22.tex) | Analytic concentration proof draft; not computationally certified |
| IE-22 | Matching universal row-deletion constant | Same joint note as IE-21 | Analytic projection/existence proof draft; not computationally certified |
| IE-23 | Nonunique induced p-to-2 norm-minimizing right inverses | [PDF](proofs/IE-23.pdf) · [Markdown](proofs/IE-23.md) · [LaTeX](proofs/IE-23.tex) | Exact right-inverse and Gram identities; continuous p range proved analytically |

[Partial rook-pivoting work](research/rook_partial.md) is separate and is **not** counted as a ninth resolution. A recovered order-five family gives an exactly checked lower-bound example at a reconstructed rational parameter.

## Run the checks

The proof-certificate checks use Python's standard library only. Run from this directory, without Python's `-O` option:

```bash
python3 verification/run_all.py
python3 verification/rook_partial.py
python3 verification/check_document_constants.py
```

The first command checks six groups of finite certificates and writes `verification/results.json`. The second writes `verification/rook_results.json`. Both commands fail on an assertion error rather than silently reporting a pass. JSON fractions are stored as exact rational strings, not rounded decimals. The row-deletion proofs are not included in the finite PASS count.

An optional, explicitly non-certifying numerical utility is available:

```bash
python3 verification/row_constants.py 0.5
```

## Rebuild the documents

The LaTeX sources are the canonical mathematical documents. Rebuilding requires a LaTeX installation containing the packages used in the sources, including `pdfpages` for the combined document. Pandoc is optional and is used to refresh Markdown renditions when available.

```bash
python3 scripts/build_documents.py
```

No LaTeX installation is needed to run the exact-arithmetic checks or read the included PDFs. No font files are distributed.

## Upload and submission review

Extract the ZIP and upload the **contents of this folder** to the intended GitHub branch or repository. Do not overwrite upstream problem statements or mark issues resolved solely on the basis of these drafts. The included [upload guide](GITHUB_UPLOAD.md), [cover note](submission-drafts/COVER_NOTE.md), and per-topic draft notes are ready for review and adaptation.

Before presenting any item as a resolved repository problem, verify its live statement and mapping, review the proof independently, and check prior work. [SOURCES.md](SOURCES.md) records source leads and retrieval limitations. **No external submission has been made.** Mathematical correctness beyond the stated checks, novelty, and acceptance are not certified.

The documents and software were developed and reconstructed with substantial AI assistance. That disclosure is included in the submission material.

## Archive integrity

`MANIFEST.json` records the file inventory. `SHA256SUMS.txt` hashes every deliverable except itself and the manifest; the manifest also records the checksum file's hash. Neither includes the ZIP containing it. Use `python3 scripts/check_integrity.py` to verify the unpacked files. Running verifiers again changes their timestamped output files; integrity checks should therefore be run before rerunning or rebuilding.
