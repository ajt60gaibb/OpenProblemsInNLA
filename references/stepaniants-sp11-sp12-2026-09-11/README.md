# SP-11 and SP-12: applications of Hall's Delta Theorem

**Application-note author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Theorem author:** H. Tracy Hall. These are literature-dependent explanatory notes, prepared with substantial ChatGPT/Codex assistance. No original discovery of Hall's theorem, the standard monotonicity property, or the chromatic implication is claimed.

**Recorded 11 September 2026.** Both exact all-graph targets are solved affirmatively by applications of Hall's [arXiv:2601.01211v1](https://arxiv.org/html/2601.01211v1), submitted 3 January 2026. The source remains a preprint. A separate independent Codex agent read and checked the full essential proof and both application notes and returned **PASS**. This is automated-agent mathematical verification, not external human peer review, formal certification, or a claim of journal acceptance.

## Exact results and source locations

| Entry | Exact conclusion | Application and primary locator |
|---|---|---|
| [SP-11](../../eigenvalues-and-inverse-problems/SP-11/README.md) | Every finite simple graph has a real symmetric exact-pattern matrix with nullity at least its minimum degree. | [Note](../../eigenvalues-and-inverse-problems/SP-11/solution.md), deduction section; Hall Theorem 3.20, Corollaries 3.22 and 3.24. [PDF](../../eigenvalues-and-inverse-problems/SP-11/solution.pdf) · [TeX](../../eigenvalues-and-inverse-problems/SP-11/solution.tex). |
| [SP-12](../../eigenvalues-and-inverse-problems/SP-12/README.md) | Every finite simple graph has a PSD exact-pattern matrix with SAP and nullity at least its chromatic number minus one. | [Note](../../eigenvalues-and-inverse-problems/SP-12/solution.md), monotonicity lemma and chromatic bound; Hall Theorem 3.20 and Corollary 3.22. [PDF](../../eigenvalues-and-inverse-problems/SP-12/solution.pdf) · [TeX](../../eigenvalues-and-inverse-problems/SP-12/solution.tex). |

SP-11 simply forgets the stronger PSD and SAP requirements in Hall's witness. Hall already states the ordinary Delta consequence. SP-12 uses a fully supplied induced-subgraph monotonicity argument and a vertex-critical induced subgraph. No connectedness restriction or assumption of Hadwiger's conjecture is added. Both canonical IDs, original targets, paths, historical ratings and attributed partial results are retained.

## Original package and withdrawn claims

The six supplied files are archived unchanged under [originals/reconstructed-notes](originals/reconstructed-notes/README.md), including their [original checksum list](originals/reconstructed-notes/SHA256SUMS.txt), [source record](originals/reconstructed-notes/SOURCES.md), [status metadata](originals/reconstructed-notes/STATUS.json), and original [SP-11](originals/reconstructed-notes/notes/SP-11.md) and [SP-12](originals/reconstructed-notes/notes/SP-12.md) notes. The [intake manifest](verification/original-package-manifest.json) hashes all six files. The original five checksums were verified against the supplied files.

The package explicitly withdraws earlier unsupported statements about a saved archive, graph-atlas computations over 1,252 inputs, code, and manifests that were not available. No such computation, artifact, or test is claimed or reconstructed here. The resolution rests on the published primary preprint and the analytical review.

The original package's preparation-stage review/eligibility limitations and date metadata are preserved as supplied. They are historical source metadata, not dates or results of this submission's checks. The actual source, mathematical-review, and public-network checks recorded here were performed on **11 September 2026**, not on 12 September. The new application manuscripts typeset the supplied arguments, expand notation so each is standalone, and add current attribution and verification metadata; the archived notes remain byte-for-byte unchanged.

## Independent mathematical review

The [complete independent review](verification/SP-11-SP-12-independent-review.md), SHA-256 `5fc9eb0cfed0af7d25415190b0fb9eaf2f16d73c6b2eead3452581870bf1eaef`, is tied to these exact supplied note hashes:

- SP-11, 2,388 bytes: `3a1c7925846cf098a23af2ce46cb5a0b27f620eb46f04bf472d4233ace962416`.
- SP-12, 5,236 bytes: `402921c079bf0cafc94020e806a5e42be4667147411b56ade228be0b7a28b61e`.

The reviewer reconstructed Hall's alternating-tensor recursion, the greedy-order bounds, and the unique leading-monomial argument even with shared variables. It then checked nonvanishing, exact graph pattern, PSD, the upper-zero-generic-to-SAP argument, and the nullity bound. It independently checked every step of the submersion proof and chromatic reduction, including rank-zero and disconnected cases.

The review also records nonessential issues in Hall v1: the abstract's definite/semidefinite typo, a missing earlier-vertex hypothesis in Proposition 5.12 whose used corollary explicitly has that hypothesis, and an unused weak-success aside that requires the subsequent nonvanishing argument. The necessary restricted statements are proved directly in the review. The independent mathematical verdict found no substantive gap in the essential all-graph proof. Unused source extensions and the separate NP-hardness appendix were not certified.

The separate [final publication-conversion review](verification/SP-11-SP-12-packaging-review.md), SHA-256 `5ff6c550e717ff0396fe4b02aed2d4d8231e2896baf60e5a3915a323dc42eebb`, also returned **PASS**. The root agent independently compared the complete archived ASCII notes with the complete typeset manuscripts, checked all canonical target suffixes and ordered formulas, and visually inspected all five application-note pages. It found no changed mathematical content or scope. This addendum preserves the original mathematical review unchanged and is automated-agent verification, not human peer review or formal certification.

## Public eligibility and source checks

The [sanitized public-network snapshot](verification/public-network.json) records the parent's audit at **2026-09-11 23:32:58 UTC**: all five recursively visible public repositories, all 32 public branch heads, 98 distinct selected text files, and 26 pull-request review bodies. Both entries remained **Partially resolved** throughout. Canonical pages, indexes, relevant text paths, issues, PRs, comments, and review bodies were examined. The only keyword match was an unrelated IE-08 issue, explicitly classified as a false positive. No already-posted full solution of either target was found in that bounded public network.

Full unrelated text and contact information are excluded from the published audit. It retains branch heads, canonical versions, paths, content hashes, and the review classification. The raw audit's digest is `0a6e2f4ee011b8eb6f2fa4137a47530618fdcd403c654306c20bf118b4f5207d`; the retained sanitized snapshot's digest is `49fbc3991bbab4ff536a547a62fc1c17fccee4ddaefd63b29f09451b74d808c6`.

The [portable read-only audit](verification/network_check.py) can be rerun with an authenticated GitHub CLI. Set `GH` to its executable if it is not on PATH and `NETWORK_OUTPUT` to the desired output path. It reads relevant text in memory and persists digests rather than unrelated bodies. Fresh keyword matches require human or agent inspection; they do not automatically establish a resolution. Private, deleted, unpublished, or unidentifiably named work is outside the audit's scope. This is not a priority determination.

A final [pre-publication refresh](verification/network-before-push.json) at **23:51:45 UTC on 11 September 2026** again found both entries Partially resolved across all five repositories and 33 branch heads, with 176 distinct selected text documents and 26 PR review bodies checked. The only match remained unrelated IE-08. Its SHA-256 is `c06f727051ac949993039418dde9c55e00f005ae9ba8a1ec232f4bd90dc1d43d`. This additional snapshot leaves the original audit unchanged.

The current [arXiv record](https://arxiv.org/abs/2601.01211) and pinned [v1 text](https://arxiv.org/html/2601.01211v1) were directly checked on 11 September 2026. Only v1 was listed and no withdrawal was displayed. A bounded later-source search did not locate a correction affecting the essential proof; the mathematical review itself, rather than absence of search results, supports the classification.

## Reproduction and checks

Run from the repository root:

```bash
python3 references/stepaniants-sp11-sp12-2026-09-11/verification/check_submission.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_solutions.py SP-11 SP-12
python3 tools/render_problems.py SP-11 SP-12
```

PDF rendering requires Pandoc and XeLaTeX; both renderers support the `PANDOC` and `XELATEX` environment overrides. The only shared-template adjustment makes the optional email block conditional; these notes supply no email. The [document checks](verification/document-checks.md) record actual validator, conversion, link, and all-page visual results. The [source checkpoints](verification/source-checkpoints.json) record exact final file hashes. These are checks of preservation and rendering, not substitute numerical evidence for an all-graph theorem.
