# Recovery report

The two earlier archives were inspected and found to contain supporting notes,
status metadata and packaging files, but no substantive manuscript or verification
code. The earlier description of their contents was incorrect. Copies of those
archives are retained under `audit/prior_archives/` solely as a record of that failure.
Their claims must not be used as the status report for this recovered package.

The present six mathematical drafts were recovered from earlier conversation
records that contained the manuscript bodies. They were reconstructed as complete
LaTeX documents, with bibliographies and visible unrefereed-candidate notices.
Problem numbers, reference names, typesetting and descriptions of evidential status
were corrected. No original manuscript files or original hashes were available,
so these are not asserted to be byte-for-byte restorations.

The recovered subjects and corrected repository identifiers are:
TR-04 (tie-aware TT-SVD), TR-06 (mean angular condition number), TR-13 (generic
odd-order Hankel ranks), TR-15 (Hankel spectral counterexample), TR-20 (rank-one
matrix discriminant degrees), and TR-26 (rational-normal-curve discriminant split).
The earlier labels TR-17 and TR-19 were incorrect for the recovered subjects.

Five diagnostic programs were restored from the earlier code records, with
formatting, paths and reporting adapted to this directory structure. The TR-20
program was reconstructed from the recovered formulas and calculation. The
unified verification driver, PDF-build helper and package-audit helpers were newly
created for this recovery. All six programs were actually run in the present
environment; fresh outputs and console logs are included in `evidence/`.

The PDFs were regenerated from the restored LaTeX sources. They contain 28 pages
in total. The LaTeX builds have no reported overfull-box or LaTeX warnings. Rendered
pages were visually inspected and extracted text was checked for substantive
content. The combined PDF contains the same six manuscripts, with bookmarks.

These recovery and packaging checks establish that the delivered archive contains
readable mathematical material and runnable diagnostic programs. They do not
establish the validity of every mathematical inference or a new resolution of a
repository problem. In particular, a finite test does not prove a universal
claim; a local algebraic check does not establish global geometric multiplicity;
and a pointwise strict approximation inequality does not yield a uniformly
smaller approximation constant.

No external submission was made. No independent referee report is available.
No three-hour active-work certification is asserted.
