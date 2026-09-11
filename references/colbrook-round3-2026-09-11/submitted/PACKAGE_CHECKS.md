# Package checks

Completed on 11 September 2026. These are artifact and reproducibility checks, not independent mathematical review.

The main verification script and the 140-decimal-digit stress script were rerun from a fresh extraction of the submission archive. Every programmed assertion passed. Both JSON results were identical to the recorded results included in this package.

The reusable sign-family generator was also checked through its command-line interface, against a dense order-169 example, and on invalid-prime, type, memory-budget, and dense-order guard cases. The default order-1,018,081 example uses the kernel representation, not a dense matrix.

Both standalone LaTeX manuscripts compile without overfull-box warnings. Their PDFs have 8 and 5 pages respectively. Every page was rendered and visually inspected; an additional bounding-box check found no text near an outer page edge. The issue bodies reproduce the complete current Markdown manuscripts, with adjusted heading levels and no omitted proof sections.

The archive contains no font files, temporary LaTeX outputs, machine-specific absolute input paths, or Python cache folders. `MANIFEST.sha256` records the individual-file digests. The ZIP integrity test passed for both the full submission archive and the optional verification attachment.

The most important mathematical limitations remain those in `START_HERE.md` and the manuscripts: IE-10 is an unreviewed full proof claim; IS-04 is an explicit-family partial result, not a solution in every dimension.
