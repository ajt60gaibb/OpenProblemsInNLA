# Full status, difficulty and impact audit — 2026-09-10

The audit covers **all 201 problem statements considered for the active catalog**:
the original 159 plus 42 additions made by the concurrent expansion. It also
rechecks and restores the historical IE-01 page. The resulting **202 retained
pages** comprise **114 Open, 86 Partially resolved, one Solved and one Solution
claimed**. Thus **200 targets remain in the open count**. The classification is
based on the exact displayed statement, not merely its title or a historical
conjecture number.

**IE-01 update — 2026-09-11:** The **Solution claimed** classification below is
historical and has been superseded by **Lean verified** after checking the paper's Lean
formalization and public Comparator verification record. See the
[retained IE-01 entry](../linear-systems-and-elimination/IE-01/README.md#lean-proof-and-verification-evidence)
for the evidence and scope. The audit's original counts below are preserved;
this status change does not affect the open count or any problem ID.

A bounded literature check cannot prove that a problem is still open. Each page
records the primary sources, relevant later results and limits of its search.
“Partially resolved” identifies substantive proved cases inside its target; a
better constant, a different oracle, a different matrix class outside the target,
or a conditional result alone does not justify that label. Several such labels
were corrected during independent review. The existence of trivial scalar or
commuting cases is not used to turn every conjecture into a partial resolution.

## Material findings

- **MI-13 is resolved affirmatively.** The [retained page and complete proof](../matrix-inequalities-and-norms/MI-13/README.md) derive its exact rectangular inequality from the established complex refined commutator bound in [Audenaert, §7.4, Corollary 5](https://arxiv.org/pdf/0907.3913). Square padding, an explicit two-unitary decomposition of a contraction, unitary invariance and the triangle inequality supply the reduction. Two additional agents independently checked dimensions, complex scalars, zero and deficient-rank cases, norm conventions and independence from the conjecture. The constant is sharp. This is a repository proof, without external peer review, Lean formalization or a novelty claim.
- **IE-01 stays outside the open count.** Its original page is restored under the stable ID, with the [September 2026 Forsythe manuscript, Theorem 1.1](https://arxiv.org/html/2609.04659v2), prominently displayed as a complete solution claim. Its theorem statement covers the original restart-length question; this catalog has not independently audited the full proof.
- **The proposed sharp Paulsen bound is withheld.** The initial source check was superseded by [Lau–Ramachandran, §7, p. 13](https://arxiv.org/pdf/2510.13751), announcing a forthcoming optimal bound. An announced proof is kept distinct from an inspected theorem. The candidate contributes no open entry.
- **Ratings changed on 27 existing entries**: 29 individual labels, because NM-01 and NM-03 changed both difficulty and impact. Nine additional draft entries received rating corrections before admission. Every current entry now explains both ratings. The resolved MI-13 page explicitly treats difficulty as historical.
- **References and scope were repaired.** Examples include IE-04’s actual Spielman–Teng source, MF-04’s publication year, the published order-four Chollet result in MI-10, the original Fallon–Iverson article in FR-09, RA-04’s SODA publication and the 2026 QRK paper in IE-21–22. Older-source evidence and inaccessible subscription text are disclosed rather than replaced by an unsupported claim of exhaustive review.

## Coverage and decisions

Each linked report has an individual decision for every allocated ID, including
retained ratings and the exact boundary between a known result and the target.
The concurrent additions are separated from the original allocation to make
coverage and counts auditable.

| Report | Current statements checked | Open | Partially resolved | Solved |
| --- | ---: | ---: | ---: | ---: |
| [Linear systems, spectral and interval problems](audit-2026-09-10-spectral-linear.md) | 53 | 39 | 14 | 0 |
| [Matrix functions and randomized approximation](audit-2026-09-10-functions-randomized.md) | 49 | 29 | 20 | 0 |
| [Tensor, positive-factorization and complexity problems](audit-2026-09-10-tensors-complexity.md) | 52 | 24 | 28 | 0 |
| [Inequalities, frames, discrepancy and final additions](audit-2026-09-10-inequalities-frames.md) | 47 | 22 | 24 | 1 |
| **Total considered for active admission** | **201** | **114** | **86** | **1** |

IE-01 is an additional restored archival page, classified Solution claimed.
The rejected Paulsen candidate is discussed in the reports but is outside this
table. The [42-entry expansion screen](EXPANSION-TO-200-2026-09.md) supplies the
new-admission source audit and distinctness decisions.

### Changes to ratings on existing entries

| Change | IDs |
| --- | --- |
| Difficulty hard → challenging | FR-04, FR-05, MD-06, MF-17, RA-05, RA-06 |
| Difficulty hard → extreme | MD-05 |
| Difficulty challenging → extreme | AC-07, AC-08, FR-10 |
| Difficulty extreme → challenging | IE-12, NM-01, NM-03 |
| Difficulty challenging → hard | IE-15 |
| Impact community → specialist | AV-02, IV-02, SP-03, SP-04, MF-13, MF-16, MI-04, MI-13, MI-15, TR-13, TR-14, TR-16 |
| Impact broad → community | FR-09, NM-01, NM-03 |

The short impact names in this table stand for the full labels defined in the
[editorial rubric](../README.md#ratings). These are comparative judgments about
scope, expected obstacles and consequences, not objectively measurable scores.
The draft additions recalibrated before admission are SP-12, IV-06, RA-17,
TR-21, TR-24, TR-28, TR-29, TR-30 and MI-25.

## GitHub display and maintained evidence

The [full catalog](../CATALOG.md) and every category index show status beside
difficulty and impact. The canonical Markdown and downloaded PDF display the
same status. Solved and claimed entries retain their IDs and original targets,
appear separately from open targets, and are highlighted in the
[resolution archive](../RESOLVED.md). Index generation reads status directly
from the canonical metadata, so resolved entries are excluded from the count.
A closed issue alone does not mean that a mathematical question is solved.

The [contributor guide](../CONTRIBUTING.md) and correction-or-resolution issue
template require an exact source, locator, outcome and comparison with the old
assumptions. An affirmative proof, counterexample and complete classification
can each resolve a question. A withdrawn claim or identified gap warrants a
revised status with the history retained.


## Document verification

All **202 canonical entries** have synchronized standalone TeX/PDF outputs,
comprising **263 pages**. Every final page was visually inspected, including
revised references/status breaks and the complete MI-13 proof. The final builds
have no overfull-box or missing-character warnings. Per-entry PDF status and
check date were compared with canonical metadata; category, catalog, archive
and canonical-page local links resolve. The original 159 displayed targets are
preserved; MI-13 adds its resolution proof after the original statement. No Lean
verification is claimed.
