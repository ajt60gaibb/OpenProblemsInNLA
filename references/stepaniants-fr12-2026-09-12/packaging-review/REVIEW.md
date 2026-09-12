# FR-12 independent publication-package review

Date: 12 September 2026 (UTC). Reviewer: Codex agent `/root/review_md03_md04`.

**Verdict: PASS for source preservation, Markdown conversion, retained target, attribution, evidence bindings, local links, and document text/privacy at the versions below.** No mathematical or document-source correction remains requested. The final outer `manifest.json` was intentionally pending during this audit and is not included in this completed-check claim. The coordinating agent must assemble it after archiving this report and verify its final file inventory.

This is a separate, read-only packaging audit. I did not author the FR-12 manuscript, alter the submission worktree, rebuild a PDF, mutate git, repeat the public-network retrieval, or publish anything. I read the complete supplied TeX, complete publication TeX and Markdown, complete canonical README and problem TeX, the independent mathematical report, the submission record, and the supporting evidence listed below. This audit is informal AI-agent review; it is not external human peer review, formal verification, or a priority certificate.

## Exact six-artifact binding

All paths in this table are within the retained canonical directory `frames-and-matrix-designs/FR-12/`.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `README.md` | 4,931 | `cd275aa531a41a8264b20c61acf9a28cea9ba5234f1ce49d2d4b7b431872f11d` |
| `problem.tex` | 8,346 | `c8db8491617e5932de994c203a66d8ecf97e0fb1ca84c714fadbe08d9d8a5716` |
| `problem.pdf` | 38,232 | `fd8a3e12e4025fb9aaef3d897f4c35b3403ba277d412903afb6f2087b97b90b6` |
| `solution.md` | 6,157 | `60ffef5d41d8986df21d25bc539f8761c86a5d64c43bb1012f110ed9917e4d59` |
| `solution.tex` | 7,371 | `700b2190651608a68c1449c065f318902180d1cc634e8845ea51d3ee5a57c163` |
| `solution.pdf` | 57,498 | `23935ddc8fd8ae69619fc34e818a581ef8b9d2b59261559bc29fb58a17fafac0` |

The frozen original and the independent reviewer's copy are byte-identical, 7,123 bytes, SHA-256 `efbcaeb82adc140be98cdffca39bf9d9a34d3b281951f42c9d7f7232279335ba`. The complete independent mathematical review is 10,930 bytes, SHA-256 `306dfae7a7d2ebe87f27ee3851b62baf8b1a4b0193d344de5eb18d226f652963`. Its five-file manifest was independently checked against the actual archived files. The review's verdict concerns the full negative counting result, not merely the finite examples.

## Preservation and conversion

The entire publication TeX from the literal `\section{Exact target}` up to, but excluding, `\end{document}` is **byte-for-byte identical** to the supplied source. This 5,438-byte interval includes both proofs, the supplementary-check discussion and table, the scope statements, and the whole bibliography. Its SHA-256 is `b9c5b21d3b305213d2afeb88a10d8a3dc9dc6e49a86a3e66402b6488481d4fa6`. The abstract is also unchanged. The only TeX differences are the PDF author metadata, visible author/affiliation, publication date, and updated pre-proof assistance/review disclosure. I read and checked the recorded exact diff.

My independently written transcription checker confirms equality of all **66 ordered mathematical expressions** between the proof TeX and Markdown, including the abstract and scope discussion. Normalization removes whitespace and equation labels/tags and expands the declared `\HH` macro to `\mathcal H`; it makes no algebraic substitutions. Both five-column table rows agree exactly: `(1,2,8,4,2)` and `(2,8,1536,192,8)`.

I also read the complete prose conversion. The Markdown keeps the deterministic ordering of matching pairs, the decoder from the first half of every row, the recovery of signs from the smaller row label, the exact matching count, every step of the recurrence iteration, and the contradiction for each fixed constant. Lemma, theorem, equation and bibliography references have the correct explicit numbers. TeX emphasis, environments and the table are converted appropriately. No hypothesis, proof step, qualification, source credit, or conclusion is lost.

## Retained canonical target and accurate scope

The original archived canonical README has SHA-256 `75985085b1cd29b2a9358692adb1573ab5c454f0befd4d991e023f37cc6cd942`. The publication README from `## Statement` through end of file is byte-identical to that original, including the source references and dated historical search statement. The new negative-resolution notice is added before it; the notice explicitly labels the subsequent material as retained history.

The target still counts individual labeled real sign matrices. No quotient by equivalence, signed row/column permutations, or automorphism groups is substituted. The universal proposed bound remains an absolute constant for every positive order divisible by four. The published result is the stronger lower bound along powers of two, sufficient to refute that universal upper-bound assertion. The notices correctly leave Hadamard existence at every admissible order and optimal counting asymptotics unsettled. Ferber, Jain and Zhao retain credit for the conjecture and prior upper bound; classical doubling is not claimed as a new operation.

All **17 ordered canonical mathematical expressions** agree between README and generated problem TeX. The `FR-12` path remains unchanged, and the complete 217-entry ID/path mapping agrees with accepted base `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. This is a direct read-only comparison, distinct from the mandatory validators and tests run by the coordinating agent.

The live README, solution sources and FR-12 `RESOLVED.md` entry prominently identify George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. They disclose substantial Codex assistance and separate informal agent review. They do not claim external human review, formal verification, or Lean verification. The proposed `Solved` status is consistent with the archived full-scope independent PASS and the contribution instructions read for this audit.

## Eligibility and archival evidence

I read the sanitized public-network snapshot and its explanatory record; I did not perform a second live crawl. The snapshot records six public repositories, 49 heads, 118 selected text blobs, 177 issue/PR/comment bodies, 39 PR-review endpoints and 32 returned review bodies at **04:45:40 UTC on 12 September 2026**. Exactly 19 heads contain FR-12 with Open status; the other 30 lack the page. The only matching discussion is the admission PR 111. The record explains its scope and exclusions and does not certify novelty.

The final snapshot checked here is 52,821 bytes, SHA-256 `6578dac408b4505e628fc65262f68e2103d39f38a103657510f0d7bc01fbcdc1`. An initial generic sentence referred to “Human assessment”; the coordinating agent corrected the sanitizer output to “coordinating agent assessment.” I checked that the final wording accurately describes this process. No original proof or mathematical review was changed.

The exact original source, independent review, five independently bound review files, author checker/output, conversion checker/output, source-preservation diff, source-search record, public audit scripts/snapshot, PDF-QA record, and coordinating verification record are present. Saved finite checks are explicitly supplementary and have appropriately bounded scopes. Historical private handoff filenames are distinguishable from the live canonical file paths; the README directs users to the latter. No third-party PDF or image is included in the reference archive inspected here.

The checker resolved all **36 live relative links** encountered in the current Markdown/TeX record and sources. The final manifest link is the one intentional assembly-time exception. Navigation inside `canonical-target.md` is retained as historical content and is explicitly identified as such in the live record, rather than silently rewritten.

## PDFs, text privacy, and required-check attribution

I independently extracted text and metadata from both unchanged PDFs without rendering or modifying them. The solution PDF has three pages and the canonical PDF has two. Both extracted texts include the full author and department/university, and neither text nor metadata contains a contact email. PDF SHA-256 values were checked before and after extraction and remained equal to the six-artifact table.

The separate packaging agent's `pdf-qa.json` records individual visual PASS for all three solution pages, with the same solution-PDF hash. The coordinating agent's `verification.json` records individual visual PASS for both canonical pages, with the same canonical-PDF hash. **I did not personally repeat visual inspection**, so those visual claims remain attributed to their actual reviewers.

The independently written source checker found no email address in the 26 then-present reference/publication text files or the FR-12 resolution entry. It is designed to retain this scan when subsequently copied into the archive, including its own source. Both exported TeX documents are standalone sources; neither depends on an external bibliography or third-party figure.

I read `verification.json`, SHA-256 `f17e5f12f92dc70363f55475a688c06b32d5c72658d1eda212652ea00d3df5ac`, which records successful ID validation against `origin/main` and the accepted base, catalog generation, all 17 permanent-ID tests and all three status tests, and actual renderer/checker runs. Those commands were run by the coordinating agent, not rerun by this packaging reviewer. No claim about later publication, CI or maintainer merge is made here.

## Reproducible scope and final assembly

`check_package.py` is a separate, standard-library, read-only packaging checker. Run it from any directory with `--repo` pointing to the checkout. During the observed final assembly, `--allow-pending-manifest` recorded the manifest as pending rather than claiming it verified. After the coordinating agent creates the outer manifest, rerun without that option; the final manifest's complete per-file digest verification is a separate coordinating assembly step.

The saved `check-output.json` binds the six artifacts and records the exact check counts. `pdf-text-check.json` binds the nonvisual PDF extraction checks. Their scope is transcription, file identity, privacy and packaging, not a machine verification of the mathematical proof.

**No outstanding source, conversion, scope, attribution, link, or privacy defect was found.** The final outer manifest and public submission are the only excluded downstream steps. The six canonical/proof artifacts should remain unchanged after this audit.
