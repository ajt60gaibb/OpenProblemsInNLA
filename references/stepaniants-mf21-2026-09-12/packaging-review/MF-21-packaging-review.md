# MF-21 independent publication-conversion and visual review

Reviewer: separate Codex agent /root/review_md03_md04.  
Date: 12 September 2026 (UTC).

**Verdict: PASS for the source conversion, reviewed-source binding, authorship/privacy checks, and all seven solution-PDF pages identified below. No correction to a canonical artifact is requested.** The coordinator must copy this report and its two companion check files into the linked packaging-review directory, then finish the final inventory. Those assembly actions are distinct from the completed source and visual review.

## Scope and independence

I did not author or edit the MF-21 mathematical manuscript or its publication sources. I read the complete publication Markdown, the complete TeX prose and formulas, the canonical notice and retained target, the reference-record prose, and the separate mathematical report. I independently wrote the read-only conversion checker linked below. I made no edits to the publication worktree, did not rebuild a PDF, and performed no public action.

The full mathematical verdict belongs to the separate agent /root/prepare_manuscripts, whose unchanged [report](../independent-review.md) is 12,545 bytes, SHA-256 3c7611724de24ce996ea313041a3d2962134e356ffa776ceef8a3df5560f6c3a. That report passes the complete three-part target for every integer m at least 3. This packaging review preserves and binds that verdict; it is not a second complete analytic proof audit, external human peer review, or formal verification.

## Frozen input and mathematical preservation

The [reviewed source](../reviewed-proof.md) is 19,393 bytes, SHA-256 98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5. Its identically retained reviewer copy is reviewed-candidate.md.

I checked the [editorial record](../editorial-conversion.json) and the separate [publication Markdown review](../publication-markdown-review.md). The three recorded repair groups remove decorative parentheses around the scalars 0 and 4, and supply missing inline delimiters around the already intended interval and quantities in Lemma 3. Applying exactly those groups to the frozen input makes Sections 1–5 byte-identical to the publication. The resulting core is 16,143 bytes, SHA-256 e75264cb480d17a2c32e6876b5949befa70bbf991f6391720cfcb0d65b799012.

I independently confirmed that the original canonical title is unchanged and that the 3,929-byte Statement-through-history suffix is preserved exactly, with SHA-256 e49bc91b60fbf057b66fd9c75dab83b8521ca5758f52f15706216bed27197672. The archived original canonical file is 4,518 bytes, SHA-256 1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f. The whole 217-entry permanent-ID registry remains byte-identical to the accepted worktree HEAD at the time of this check.

## Markdown, TeX, links, and attribution

The independent [checker](check_packaging.py) and [exact output](independent-conversion-check.json) establish:

- All 260 ordered mathematical expressions in solution.md agree with solution.tex after removing mathematical whitespace only.
- All 34 ordered mathematical expressions in the canonical README agree with problem.tex under the same comparison.
- The entire visible solution prose and the canonical body beginning with the rating rationale agree through the independent Markdown and TeX readers after typographic normalization of whitespace, quotes, and dash characters. No unexamined raw content remains after removing the known layout directives.
- All nine solution links and fourteen canonical-body links retain their labels and intended targets. Repository-relative Markdown destinations are expanded to the corresponding upstream-main URLs in TeX.

The manual read confirms the theorem and lemma labels, all bounds and equation references, the proof transitions, the external-kernel attribution, and the source-scope limitations. The only layout commands removed for the prose comparison are Needspace, nopagebreak, and newpage; no mathematical or expository passage is discarded.

The visible author is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. This byline appears in the solution, canonical resolution notice, and MF-21 RESOLVED entry. The solution PDF metadata also names George Stepaniants. The canonical problem PDF retains the collection's document-author metadata and prominently includes the resolution author's full visible byline.

The conjecture and prior special cases retain attribution to Barrera, Böttcher, Grudsky, Maximenko, and the later cited authors. Böttcher–Widom and their cited predecessors retain credit for the inverse-kernel result. The submission explicitly discloses substantial AI assistance and the limits of an informal independent AI audit.

No contact email or mailto address was found in the scanned publication sources, the reference archive, the MF-21 resolution notice, either PDF's metadata, or either PDF's extracted text. The email-address pattern is checked in every text file, including code; the literal mailto marker is checked in non-code files so the checker's own test string is not misidentified as a published address.

## Reference bindings and bounded evidence

I checked all eight entries in the independent-review manifest, all nine historical supporting entries, and all three source-scope-manifest entries against actual bytes, using the filename mappings expressly documented by the submission record. The linked independent-review.md is byte-identical to the original independent-math-review.md.

The historical RESULT.md name maps to reviewed-proof.md. The historical author-check output maps to original-exact-check.json and retains its original digest. For the adapted author checker, replacing its reviewed-proof.md filename references by RESULT.md reconstructs the original checker bytes and digest exactly. Thus its only change is the documented source filename adaptation; the new output correctly records the adapted checker. The original pending-review wording remains historical and is superseded by the unchanged signed PASS.

At the completed-reference checkpoint, 54 relative Markdown links were examined. All targets exist except the intentional link to this report, which the coordinator must satisfy by copying the report into its declared directory. Navigation inside the two frozen canonical snapshots was interpreted at its original canonical location, as the submission record explicitly explains. There are no unexplained missing links. After the report and companion files are copied, rerunning the checker without the pending-assembly option must also pass.

No PDF or image asset is present in the reference archive. The retained public-network record contains sanitized metadata and fingerprints rather than retrieved third-party papers or discussion bodies. I checked its consistency with the archive prose: its recorded 03:37:45 UTC search covers six public repositories, 48 branch heads, 232 selected text blobs, 175 issue/PR/comment bodies, and 32 review bodies from 38 endpoints. It reports Open on every returned MF-21 page and no matching competing discussion. I did not repeat that network retrieval or certify priority. The separately retained final head refresh is coordinating evidence; I did not repeat its network requests.

The coordinating verification record records the required 17 ID tests, three status tests, both base validations, and the exact-checker reruns as passing. I checked that their scope is stated separately from the full mathematical proof; I did not rerun those repository tests in this review.

## Seven-page solution-PDF visual inspection

I individually opened each of the seven final page PNGs using view_image. I checked every page's visible text, equations, headings, byline, page breaks, footers, page numbers, and references. No clipping, overlapping elements, unreadable glyphs, displaced equation numbers, or broken reference text was found. Equations (1)–(33) and the four bibliography entries are readable.

The inspected solution PDF has seven pages and 101,652 bytes. Its SHA-256 was 829d4e48d9ff61869465faf0470f9ff51f50beeee4fab5d46b191c5c4b9a3c8e both before and after visual inspection, and is unchanged during the subsequent source review.

I did not visually inspect the canonical problem PDF in this task. The coordinator separately records inspection of both final pages. My checks confirm its current two-page count, text/metadata privacy, and the preserved Markdown/TeX conversion.

## Exact artifact versions

All paths below are relative to matrix-functions-and-stability/MF-21/.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| solution.md | 19,864 | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| solution.tex | 23,434 | 1baff64e748b8a3a31d53f1727560937e5c84524a202a25bc92c081b4f1fcd49 |
| solution.pdf | 101,652 | 829d4e48d9ff61869465faf0470f9ff51f50beeee4fab5d46b191c5c4b9a3c8e |
| README.md | 6,599 | 2b73eab3bd1bdba6619913b9713606aafc3deb6a0b4684afae92b7581ea2ed17 |
| problem.tex | 10,309 | 437a9eb8db9672b7695ae436a32a444df6fd3f08a180ee6070e0e8739763490d |
| problem.pdf | 44,607 | 4a0611580170020c9b06e9f57512e646794cd2e93dff846452532d4806cdfcbd |

The canonical TeX/PDF hashes here identify the coordinator's final layout-only two-page render. They replace the earlier canonical artifact fingerprints in the initial private core-comparison output; the source target and mathematical-expression comparisons did not change.

For a final read-only rerun from the repository root after copying this report and its two companion files, set PANDOC if needed and use:

    python3 references/stepaniants-mf21-2026-09-12/packaging-review/check_packaging.py . --complete-references

This review is bound to the artifact versions above. Later mathematical, source, or PDF changes require another corresponding check. Adding the dated head-refresh record and the final assembly fingerprints does not change the reviewed proof or visual result.

Signed electronically by the separate Codex reviewing agent /root/review_md03_md04, 12 September 2026 (UTC).
