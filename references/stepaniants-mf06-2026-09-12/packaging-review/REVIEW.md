# MF-06 independent publication-conversion review

**Verdict: PASS for the final mathematical publication, retained canonical target, attribution, and the inspected package records.** The complete original MF-06 assertion remains the scope of the solution. No mathematical change was introduced in publication conversion. One document-encoding defect found during this review was corrected and rechecked. No source or PDF correction remains outstanding.

**Reviewer:** Codex agent `review_aa01`, 12 September 2026, 05:28:35 UTC. I independently reviewed the complete mathematical candidate earlier, but did not author the publication Markdown, TeX, builder or document layout. This report is a separate conversion and package audit. It is informal AI-agent review, not external human peer review or formal verification.

At this report's freeze, the final six canonical artifacts and the coordinating verification record are frozen. The coordinator still has to copy this report into its linked archive location and generate the outer publication manifest. Those two assembly items are explicitly reported by the saved checker output; they are not represented as already completed. A final invocation with `--require-final-records` is provided below to require their presence. Git actions, publication, CI and maintainer merge are outside this review.

## 1. Exact reviewed inputs and final artifacts

The full clarified mathematical candidate is [reviewed-proof-clarified.md](../reviewed-proof-clarified.md), 15,842 bytes, SHA-256 `11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94`. Its first full version is [reviewed-proof.md](../reviewed-proof.md), 15,815 bytes, SHA-256 `2471cce689608c9ff0dfe15e4ed0230f00ba6799c4df1129e593f08e50593f2d`. I verified both archived files byte-for-byte through their frozen hashes.

The separate complete [mathematical review](../REVIEW.md) is unchanged: 18,353 bytes, SHA-256 `6c15e3d3a20669ede243d7e56d1229f148e39a138e7c0d1628c5768cf6166d36`. Its verdict independently reconstructs both the product-bounded-family argument and the full exterior-power extension. An earlier review of only the partial argument is not used as a premise for full-scope PASS.

The canonical artifact paths below are relative to `matrix-functions-and-stability/MF-06/`.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| README.md | 4,487 | `88ed3327ef3da4ba1dcc31bc93f7f5c28c76fd660bfcdf8af3cd5158caa0718b` |
| solution.md | 18,632 | `c9cb85b51fdb336c53db88a64e4a8b73f76af9b3e76a8f46851e96683cf000a4` |
| solution.tex | 20,665 | `7cef28e1180d11d493d38a2cab6c557e88b8d789d2b1c90f45917cf908d5614f` |
| solution.pdf | 76,377 | `31a6e33d8508e8f323fe2629dd7338c12601da0867c906ad20f58640f0bff2bd` |
| problem.tex | 7,997 | `53d6c21d3d66333378bd0ea6c98a248152f999c99242a5e96c009997bb1cf821` |
| problem.pdf | 33,368 | `c77d630f09c60106a054f08fcb6a07f78ef1e3f3ca7fbf1a8048076d29d63154` |

These are the final corrected artifacts, not the earlier PDF with two incorrectly encoded section signs.

## 2. Complete mathematical and prose preservation

I read the full publication Markdown and TeX, including the complete argument, scope discussion and bibliography. I also wrote a separate read-only checker, [check_package.py](check_package.py); it does not import or invoke the publication builder, the packager's checker, or the mathematical author's code.

The full source range from `## 1. The exact target` through the end of Section 6, stopping before `## 7. Scope of verification and attribution`, is **byte-identical** between the clarified reviewed source and publication Markdown. The range has 14,325 UTF-8 bytes and SHA-256 `95ffa57f417ac6e0bbc5e43da9f890d92384126f2cac41e2f282898ffb18bc4a`. This comparison includes all prose and hypotheses, not only equations or theorem statements.

All **182 ordered mathematical expressions**, including inline expressions, display formulas, tags and the five existing proof-end squares, agree between the Markdown and final TeX after removing whitespace inside each expression. Dollar delimiters become the usual LaTeX inline/display delimiters. No mathematical token is added, omitted or changed. This checks the nonnegative-parameter clarification, paired-generator definitions, scalar estimates, allocation degrees, maximal critical degree, Hausdorff bounds and final root inequality in their original order.

I separately compared the complete post-title publication prose from the introductory paragraph through the final reference. The checker substitutes numbered placeholders for formulas, preserves every remaining word, number and punctuation mark, and reverses only enumerated presentation syntax: headings, bold/italic formatting, hyperlinks, list markers, nonbreaking spaces, TeX dash encoding, the recorded page-space directives and QED alignment. Unknown TeX commands in the prose cause failure. The two normalized texts are identical: 16,854 UTF-8 bytes, SHA-256 `0aad326f135b30f9358c8c795621ab24651ad4c44cbd3b2391089caae7ed6fa0`. Link target sequences are also identical between the proof Markdown and TeX.

The [recorded layout difference](../latex-layout-changes.json) contains two `Needspace` directives, 27 nonbreaking numerical references, one nonbreaking family-index space, right alignment of five existing proof-end squares, and the two explicit section-sign encodings discussed below. These changes are outside mathematics. The title, author and affiliation are intentionally moved into the standalone TeX title block and were checked separately.

The only change between the two frozen mathematical candidates is the recorded insertion `Let $n\ge1$ and $K,F\ge0$.` in Lemma 2. The checker deletes that single insertion and recovers the original candidate exactly. The [clarification diff](../source-clarification.diff), [clarification record](../source-clarification.json), independent checker, saved finite-check output and [independent manifest](../independent-manifest.json) retain their signed hashes. No original review was rewritten to make the publication appear reviewed earlier than it was.

## 3. Full original target and canonical history

The archived [canonical target](../canonical-target.md) has 2,607 bytes and SHA-256 `fe32efa1f84a750039f65695f3cadbf615ead558826490e53329ca26704df741`, the exact target reviewed mathematically and audited against the public base. In the current canonical README, the **entire suffix from `## Context and notation` through the end of the historical audit is byte-identical**: 2,031 bytes, SHA-256 `6b6c8cafeff856626af1ffa8d340bb359c6de41748e8ca9874f3883dc3c3d3dd`. All 11 ordered mathematical expressions in the complete current canonical README also match its generated problem TeX.

The result covers every finite complex dimension and every nonempty compact fixed reference family, including reducible references with unbounded normalized products. The constants may depend on that fixed reference; the perturbing family may be arbitrary. The zero-radius case, normalization, product-bounded reduction, maximal critical exterior degree and transfer are preserved. The new notice neither substitutes a finite-family question nor imposes invariant-subspace preservation or periodic attainment. It does not claim the different two-sided uniform estimate associated with MF-05.

The current registry still maps `MF-06` to `matrix-functions-and-stability/MF-06/README.md`, among 217 registered IDs. I made no registry or repository edits. The coordinator's [verification record](../verification.json) separately records the published-base ID checks and required repository tests; I did not rerun them during this read-only conversion task. The retained historical text is expressly identified as historical, so its earlier unresolved status is not a present competing status claim.

## 4. Attribution, review status and privacy

The visible byline in the proof and canonical documents is **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**. The solution PDF's author metadata is George Stepaniants; the canonical generated PDF retains the repository's standard document-author metadata while visibly attributing this solution to George. No contact email appears in either PDF's text or metadata, or in the 29 public text files checked before this report is copied.

The manuscript correctly credits Epperlein and Wirth for the target and standard joint-spectral-radius context. Barabanov/Wirth extremal-norm theory is acknowledged, with a direct Wirth locator in the submission record. The prior nonresonance/product-boundedness theory and transition-sum mechanism of Chitour, Mason and Sigalotti are credited with the specific discrete-time and appendix locators. The proof makes no novelty claim for that general mechanism. Morris's related second-exterior criterion is stated with its product-boundedness assumption; it is not cited as already proving the maximal-critical-degree lemma. The required reduction is proved within the unchanged core.

The proof, canonical notice and submission record disclose substantial AI assistance and distinguish the separate full mathematical audit from finite transcription checks. `Solved` is scoped to the full original assertion under the repository's informal independent-review process. There is no claim of human peer review, formal verification, historical-priority certification, two-sided uniform Lipschitz continuity, CI success after publication or completed maintainer merge.

I read and verified the unchanged public/source audit files and their frozen hashes. The original six-repository, 49-head audit and the coordinator's subsequent 50-head refresh are dated and bounded; the new head is the separate FR-12 branch, not a competing MF-06 resolution. Retrieved full discussion bodies and third-party primary PDFs are not bundled in this archive. Historical private scratch labels in exact frozen proof snapshots are evidence of their original staging context, not live reproduction dependencies.

## 5. Links and reproducibility

The independent checker inspects the live canonical README, proof Markdown and submission README. It found 34 relative-link occurrences: 32 resolve at this report's freeze, and the remaining two are exactly this report's intended archive location and the outer manifest that the coordinator is about to generate. No other broken live local link was found. The frozen canonical copy's old navigation is explicitly marked historical rather than treated as live navigation.

This conversion task was offline: I did not make network calls. External URLs are inventoried and checked for faithful conversion, while source accessibility is attributed to the separate dated source audit. During the final pass the coordinator additionally reported opening the exact Morris HTML URL `https://arxiv.org/html/0909.2800v1` and the Epperlein–Wirth v2 HTML directly; the Morris record returned the correct title, version and Lemma 3.2. That availability check belongs to the coordinator, not to this offline checker.

Both private checker scripts are portable and read-only. From the repository root, after the package is copied:

```sh
python3 references/stepaniants-mf06-2026-09-12/packaging-review/check_package.py --repo . --require-final-records
python3 references/stepaniants-mf06-2026-09-12/packaging-review/check_pdf_text.py --repo .
```

The first uses only the Python standard library and reads sources, hashes, recorded metadata and local link targets. It never executes the publication's scripts or fetches anything. The second requires Poppler `pdfinfo` and `pdftotext` on `PATH`; it only reads already-built PDFs and prints JSON. Neither compiles or renders documents, mutates the repository, invokes git or runs repository tests. Their outputs at this freeze are [source-comparison.json](source-comparison.json) and [pdf-text-check.json](pdf-text-check.json).

## 6. Document inspection and corrected encoding finding

I independently extracted and read the text of both final PDFs and inspected their metadata. The proof has seven A4 pages and the canonical problem has two A4 pages. Both contain the full visible byline and affiliation, disclose informal AI-agent review, are unencrypted and have no JavaScript. The final extracted text has no replacement character or the incorrect section-sign glyph flagged below. Metadata and byte hashes agree with the frozen artifacts and final QA records.

During the first PDF text pass, two literal section signs in the proof extracted as a different letter. I asked the document reviewer to inspect those exact locations. The reviewer confirmed the visual glyph error and corrected only the two prose characters in generated TeX to explicit `\S{}` commands. I independently rechecked full prose and all 182 formulas against the original Markdown after this correction. Both final references now extract correctly as section signs. The correction is encoded in the builder and recorded in the layout difference; it changes no mathematical statement.

**Visual inspection is attributed to the people who performed it:** Codex agent `prepare_manuscripts` individually inspected all seven final proof pages, including a complete reinspection after the section-sign correction. The coordinating Codex agent individually inspected both canonical pages. Their separate [proof QA](../pdf-qa.json) and [canonical QA](../canonical-pdf-qa.json) reports are bound to the final PDFs. I did not render pages or claim those visual inspections as my own. The proof reviewer records two successful final XeLaTeX passes with no warnings or over/underfull boxes; the coordinator records the successful canonical renderer run.

## 7. Record consistency and remaining assembly

The final [verification record](../verification.json) has 4,592 bytes and SHA-256 `0509d4d2a2896d5ebf8b2584309a1ff788d76a1f86e49937fd0116d7b2d388ed`. I read it and independently matched its mathematical-review, canonical-tail and final PDF bindings. The source-preservation, packager-conversion, layout and both document-QA records also refer to the final corrected artifacts. Their hashes, the final builder/checker hashes and the frozen independent/source-audit hashes are retained in `source-comparison.json`. Stale staging handoff metadata was removed from the public archive; the exact mathematical evidence remains unchanged.

Only the assembly of this signed report and the outer manifest remains at the instant recorded here. The coordinator can close that mechanical check by copying these files, generating its repository-relative manifest, verifying every manifest digest and running the provided checker with `--require-final-records`. No further mathematical, source-conversion, attribution, privacy or document correction is requested by this review.

**Signed:** Codex agent `review_aa01`, independent publication-conversion reviewer, 12 September 2026, 05:28:35 UTC.
