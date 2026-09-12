# Independent publication review: Lean PRs 172, 173, 174, 182

**Verdict: PASS for preservation, publication metadata, and authored file scope. All ten changed canonical PDF pages were visually inspected. One nonblocking pagination improvement is identified for FR-12 below.**

Reviewers: Codex AI agents `/root/audit_spectral_linear` (TR-15, FR-12 and synthesis) and `/root/audit_spectral_linear/ie16_pr178` (RA-07, MI-23), 12 September 2026. This is a bounded publication review, not a new certification of the Lean proofs or CI artifacts. The coordinating reviewer owns those separate checks. No repository or remote state was changed; no submitted code, CI, or checksum procedure was run.

| PR | Problem | Exact head | Canonical PDF pages inspected | Publication result |
| --- | --- | --- | --- | --- |
| 172 | RA-07 | `185a7c394b3c89a28cc0daaab12cc54de6c04173` | 1–2 (all 2) | PASS |
| 173 | MI-23 | `af65452c26fba4223555fa302d318a2ca50457c3` | 1–3 (all 3) | PASS |
| 174 | TR-15 | `856b1618b1cad046b3640a13de0df5ef4c10a8f3` | 1–2 (all 2) | PASS |
| 182 | FR-12 | `0212a62c25e02f38a74ce9af5504e37630309a3f` | 1–3 (all 3) | PASS; minor reference pagination |

## Targets, scope, and credits

The original statement sections and their following source/status material remain exactly unchanged against published main `f41f1f9ffa2171550d4bb795862c6170c4f26070` for all four entries. The permanent identifiers and mathematical questions are retained. Canonical README, TeX/PDF, and index changes present the later Lean record separately from the historical informal resolution. The visible status is `Lean verified`, dated 2026-09-12; no source-reviewed informal proof is mislabeled as itself a formal proof.

- **RA-07:** The positive-tuple domain, elementary symmetric sums and conventions, ratio sequence, and full index range survive unchanged. New text limits the formal exports to scalar convexity rather than claiming extra sampling/application results. Colbrook's mathematical authorship/Cambridge affiliation and Stepaniants's formalization/Caltech affiliation remain distinct, with AI assistance disclosed.
- **MI-23:** The complex positive-definite domain, exponent and interpolation ranges, generalized mean, ordered eigenvalue-product prefix inequalities and total-product equality remain unchanged. The distinction from the older singular-value conjecture survives. The Colbrook/Stepaniants mathematical/formalization credits are retained and distinguished as above.
- **TR-15:** The original lower/upper tensor-network inequality and all its assumptions remain unchanged. New text describes the actual `m=3, q=2, n=2` witness, `h=(2,0,1,0,2,0,-1)`, the nonvacuous lower premise, and the upper violation. It preserves the original mathematical proof links and Colbrook credit, adds Stepaniants's formalization credit with AI assistance, and distinguishes the historical informal audit from the later Lean claim.
- **FR-12:** The actual labeled real Hadamard-matrix counting problem and original lower/upper bounds remain unchanged, including Ferber–Jain–Zhao attribution. Stepaniants's mathematical and Lean credit and AI assistance remain explicit. The formal scope carefully states the weaker recurrence `m! H(m)^2 ≤ H(2m)` and separates the stronger informal `(2m−1)!!` recurrence from the exported Lean theorems. It claims the resulting power-of-two quantitative lower bound and negation of every positive-real exponential constant, not an unexported stronger recurrence.

The isolated index count changes are consistent with moving one retained result from `Solved` to `Lean verified` in each branch; unresolved counts do not change. Combined integration should regenerate counts rather than copying any one branch's isolated totals.

## PDF inspection

Using the PDF skill and Poppler, we inspected the actual committed canonical `problem.pdf` files at readable resolution. All titles, statuses, mathematics, credits, references, theorem/export names and page numbers are legible. No clipping, overlap, missing mathematical glyphs, stale status, or material Markdown/TeX/PDF mismatch was found. The RA-07 and MI-23 page review is detailed in `/private/tmp/nla-batch-lean-publication-172-173.md`. The TR-15 and FR-12 renders are under `/private/tmp/nla-batch-lean-pdf-review/`.

**Nonblocking FR-12 pagination:** Page 2 ends with the `References and status check` heading and its first reference; page 3 starts with the remaining two references and historical status paragraph, leaving substantial blank space. A deliberate page break immediately before that heading would keep the reference/status section together on page 3 without changing any mathematics or evidence. All existing text is present and readable, so this is polish, not a correctness blocker. TR-15's two-page layout needs no adjustment.

Canonical PDF locations reviewed:

- `/private/tmp/nla-audit-172/randomized-and-low-rank-approximation/RA-07/problem.pdf`
- `/private/tmp/nla-audit-173/matrix-inequalities-and-norms/MI-23/problem.pdf`
- `/private/tmp/nla-audit-174/tensor-computations/TR-15/problem.pdf`
- `/private/tmp/nla-audit-182/frames-and-matrix-designs/FR-12/problem.pdf`

## Complete authored file scope

Complete Git diffs were used; PR metadata file arrays are truncated and are not sufficient for this check.

| PR | Actual merge base | Changed paths | Paths inside its own problem's Lean directory | Remaining paths |
| --- | --- | --- | --- | --- |
| 172 | `c0601d8825e9f9e744212c62e6a43fefc1c60a22` | 400 | 393 | Canonical README/TeX/PDF plus four indexes |
| 173 | `f41f1f9ffa2171550d4bb795862c6170c4f26070` | 421 | 414 | Same permitted seven paths |
| 174 | `f41f1f9ffa2171550d4bb795862c6170c4f26070` | 433 | 426 | Same permitted seven paths |
| 182 | `f41f1f9ffa2171550d4bb795862c6170c4f26070` | 436 | 429 | Same permitted seven paths |

The four indexes are root `README.md`, `CATALOG.md`, `RESOLVED.md`, and the relevant category README. No authored unrelated canonical target, original informal solution, permanent-ID registry, shared renderer, guard, or workflow changes were found. All remaining additions are within the corresponding problem's Lean project/evidence tree.

**PR 172 baseline caveat:** Its branch predates later main's AV-03/IV-01 additions. A direct comparison of its tip with the newer base has 474 paths and can misleadingly look like deletion of those later additions. The actual merge-base diff contains only the scoped 400 paths above. Integration must retain later upstream AV-03/IV-01 content; this report approves merging the authored delta, not replacing current main with PR 172's older complete tree.

The publication layer passes at the exact heads listed. Proof soundness, authenticated Lean evidence, and the eventual combined integration tree remain the coordinating reviewer's separate responsibility.
