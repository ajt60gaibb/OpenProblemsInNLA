# Submission checks — 12 September 2026

The coordinating agent verified that each canonical README is byte-for-byte identical to upstream main after removing its new notice and restoring the original Status/Last checked metadata. The permanent registry is unchanged. All four PDFs were rebuilt with the repository renderer and all seven pages were rendered to PNG and visually inspected for clipping and malformed mathematics.

Passed: permanent ID validation against origin/main; catalog generation; 17 permanent-ID tests; 3 status tests; 16 math-formatting tests; 11 rendering tests with Pandoc available; repository-wide math-format check; git diff whitespace check. No Lean verification was performed.

The copied reviewer-owned MI-15 supplemental script was made portable by changing only its source-directory path and was rerun: 125 integer matrix/quartic/Gram comparisons passed and five diagonal corruptions were rejected.
