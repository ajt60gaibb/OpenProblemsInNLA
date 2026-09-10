# Spectral, linear-system, and interval audit — 2026-09-10

Scope: all 44 canonical entries in linear-systems-and-elimination (19), eigenvalues-and-inverse-problems (20), and intervals-and-absolute-value-equations (5). Each full statement and its rating labels was reviewed; each ID received targeted later-resolution searches and primary-source checking. The dated section in each linked entry records its particular evidence. No newly established full solution was located. Search absence is bounded evidence, not proof of present openness.

“Partially resolved” denotes a substantive proved subclass or parameter range of the displayed target, including results predating this audit. Weaker bounds, related algorithms, different input/oracle models, numerical evidence, and cases excluded from the displayed target do not automatically earn that label. The rating decisions are editorial assessments under the repository rubric, not author-assigned difficulty claims.

Material corrections and boundaries:

- IE-04's linked Spielman–Teng chapter had the wrong title; corrected to *Smoothed Analysis of Algorithms and Heuristics: Progress and Open Questions* and added its chapter DOI. Conjecture 16 and the mathematical statement are unchanged.
- IV-02 records the polynomial exact determinant-range algorithm for the substantive tridiagonal interval H-matrix subclass; the unrestricted tridiagonal question remains unresolved. This corrects an initially missed partial-status implication during the PDF review.
- SP-09 now records the all-dimensional self-adjoint case in Corollary 3.5 of the direct follow-up. Its general normal-matrix question remains unresolved in the checked literature.
- IE-12's remaining general-system gap is removal of dimension-dependent logarithmic overhead. Its positive definite subclass meets the requested cost; difficulty is recalibrated accordingly.
- IS-04's asymptotic theorem implies the target for sufficiently large dimensions. The explicit cutoff in the source assumes the Hadamard conjecture; it is not an unconditional solution of the remaining finite range.
- Added the 2026 Cai–Chen–Ma–Wu QRK subsample-size publication to IE-21/22 as related progress that does not determine either displayed row-deletion quantity, and the 2018 journal publication of the IS-03 primary paper.
- Historical openness in IE-13/14/15/16/19/23, IS-02, SP-03, and IV-02 is expressly bounded by the sources and follow-up searches. No inaccessible source body was used to assert a new theorem. Source-host retrieval failures were followed by accessible author or publisher copies where available.
- SP-06 remains a conjecture because its original proof was withdrawn in an erratum; SP-07 asks for the optimal constant after the constant-one conjecture was refuted. Neither should be marked solved merely by reading an older theorem/conjecture title.

| ID | Verdict | Evidence checked | Rating decision |
|---|---|---|---|
| [AV-01](../intervals-and-absolute-value-equations/AV-01/README.md) | Open | Hladík (2026), §2.3; maximum-count complexity search. | Retained challenging / specialist. |
| [AV-02](../intervals-and-absolute-value-equations/AV-02/README.md) | Open | 2025 AVE survey §5.4; Zamani–Hladík condition-number paper. | **impact community → specialist**. |
| [AV-03](../intervals-and-absolute-value-equations/AV-03/README.md) | Open | AVE survey §2.4.2; 2605.10701v2. | Retained extreme / broad. |
| [IE-02](../linear-systems-and-elimination/IE-02/README.md) | Partially resolved | Tichý–Liesen–Faber §§3–5; 2506.09687 §§4–5. | Retained challenging / specialist. |
| [IE-03](../linear-systems-and-elimination/IE-03/README.md) | Partially resolved | Peca-Medlin (2026), §3; Higham Problem 9.17. | Retained extreme / community. |
| [IE-04](../linear-systems-and-elimination/IE-04/README.md) | Open | Spielman–Teng Conjecture 16; Huang–Tikhomirov (2024). | Retained extreme / broad. |
| [IE-05](../linear-systems-and-elimination/IE-05/README.md) | Open | 2308.16146v2 §3.2, Appendix B; SIAM 2024 publication. | Retained challenging / specialist. |
| [IE-06](../linear-systems-and-elimination/IE-06/README.md) | Open | Huang–Tikhomirov (2024), abstract and introduction. | Retained challenging / community. |
| [IE-07](../eigenvalues-and-inverse-problems/IE-07/README.md) | Open | 2602.05394v3, Problem 3.1; deterministic regularization search. | Retained extreme / broad. |
| [IE-08](../eigenvalues-and-inverse-problems/IE-08/README.md) | Open | 2602.05394v3, Problem 3.3; cubic Schur precision search. | Retained extreme / broad. |
| [IE-10](../eigenvalues-and-inverse-problems/IE-10/README.md) | Open | 2602.05394v3, Problem 3.5 and update; cyclic Krylov search. | Retained challenging / specialist. |
| [IE-11](../linear-systems-and-elimination/IE-11/README.md) | Open | Chen–Edelman–Urschel, 2602.20390, abstract and conjecture. | Retained challenging / specialist. |
| [IE-12](../linear-systems-and-elimination/IE-12/README.md) | Partially resolved | 2604.16075v2, Corollaries 17, 25 and §7. | **difficulty extreme → challenging**. |
| [IE-13](../linear-systems-and-elimination/IE-13/README.md) | Open | Higham (2002), Problem 9.15(a); later bandwidth/growth search. | Retained challenging / specialist. |
| [IE-14](../linear-systems-and-elimination/IE-14/README.md) | Open | Higham (2002), Problem 9.15(b); cyclic/quasi-tridiagonal growth search. | Retained challenging / specialist. |
| [IE-15](../linear-systems-and-elimination/IE-15/README.md) | Open | Higham (2002), Problem 9.18; exact small-order rook search. | **difficulty challenging → hard**. |
| [IE-16](../linear-systems-and-elimination/IE-16/README.md) | Partially resolved | Liesen–Tichý (2004), §§3.2.1–3.2.2, conjecture (3.16). | Retained challenging / community. |
| [IE-17](../linear-systems-and-elimination/IE-17/README.md) | Open | Fong dissertation §7.2.1, p. 118; Hallman 2605.09211. | Retained challenging / community. |
| [IE-18](../linear-systems-and-elimination/IE-18/README.md) | Open | 2312.04776v4, Conjecture 10; SISC 2025 publication. | Retained challenging / community. |
| [IE-19](../linear-systems-and-elimination/IE-19/README.md) | Open | 1203.6812, §8, Conjecture 8.1. | Retained challenging / specialist. |
| [IE-20](../linear-systems-and-elimination/IE-20/README.md) | Open | 2602.05394v3, Problem 2.17; finite-precision CG search. | Retained extreme / community. |
| [IE-21](../linear-systems-and-elimination/IE-21/README.md) | Open | Steinerberger §2.3; 2608.27968v1; Cai et al. SIMAX 2026. | Retained challenging / community. |
| [IE-22](../linear-systems-and-elimination/IE-22/README.md) | Open | Steinerberger §2.3; Cai et al. SIMAX 2026. | Retained challenging / community. |
| [IE-23](../linear-systems-and-elimination/IE-23/README.md) | Open | Dokmanić–Gribonval, Corollary 4.2(3), Remark 4.1. | Retained hard / specialist. |
| [IS-01](../eigenvalues-and-inverse-problems/IS-01/README.md) | Open | 1908.03647; ILAS 2026 abstracts, p. 150. | Retained challenging / community. |
| [IS-02](../eigenvalues-and-inverse-problems/IS-02/README.md) | Open | 1310.1273, §5, Conjecture 5.1; later spectral-uniqueness search. | Retained challenging / specialist. |
| [IS-03](../eigenvalues-and-inverse-problems/IS-03/README.md) | Partially resolved | 1712.05454, Conjecture 1.2 and proved families; LAA 2018. | Retained challenging / community. |
| [IS-04](../eigenvalues-and-inverse-problems/IS-04/README.md) | Partially resolved | 2511.14653v1, theorem and §6, Problem 12. | Retained challenging / community. |
| [IS-05](../eigenvalues-and-inverse-problems/IS-05/README.md) | Open | 2511.14653v1, Problem 11; Steinerberger Problem 69. | Retained extreme / community. |
| [IV-01](../intervals-and-absolute-value-equations/IV-01/README.md) | Partially resolved | Adm–Garloff (2026), §3, Theorems 3.2–3.3. | Retained challenging / specialist. |
| [IV-02](../intervals-and-absolute-value-equations/IV-02/README.md) | Partially resolved | Hladík, §5.4 after Proposition 5.6; interval determinant-range search. | **impact community → specialist**. |
| [KE-01](../linear-systems-and-elimination/KE-01/README.md) | Open | 2602.05394v3, Problem 2.5; Liu et al., Theorem 1.1. | Retained challenging / community. |
| [KE-02](../eigenvalues-and-inverse-problems/KE-02/README.md) | Open | 2602.05394v3, Problem 3.2; deterministic Minami search. | Retained challenging / community. |
| [KE-03](../eigenvalues-and-inverse-problems/KE-03/README.md) | Open | 2602.05394v3, Problem 3.9; nonnormal eigenvalue-query search. | Retained challenging / community. |
| [KE-04](../eigenvalues-and-inverse-problems/KE-04/README.md) | Open | 2507.16484v1, conjecture and concluding discussion. | Retained challenging / community. |
| [SP-01](../eigenvalues-and-inverse-problems/SP-01/README.md) | Open | 1412.6294; Operators and Matrices 15 (2021), article 74. | Retained challenging / community. |
| [SP-02](../eigenvalues-and-inverse-problems/SP-02/README.md) | Open | 1412.6294; 2021 follow-up; off-diagonal threshold search. | Retained challenging / community. |
| [SP-03](../eigenvalues-and-inverse-problems/SP-03/README.md) | Open | Baaijens–Draisma (2015), §5; symplectic ED-degree search. | **impact community → specialist**. |
| [SP-04](../eigenvalues-and-inverse-problems/SP-04/README.md) | Open | Baaijens–Draisma Problem 4.3; Sander 2501.19310 introduction. | **impact community → specialist**. |
| [SP-05](../eigenvalues-and-inverse-problems/SP-05/README.md) | Open | 1805.09737, Conjecture 1 and equation (7). | Retained challenging / community. |
| [SP-06](../eigenvalues-and-inverse-problems/SP-06/README.md) | Open | 1702.00741v4, appended erratum; 2411.16266. | Retained challenging / community. |
| [SP-07](../eigenvalues-and-inverse-problems/SP-07/README.md) | Open | 2603.23056, Proposition 3.4; Holbrook lower bound and historical surveys. | Retained extreme / community. |
| [SP-08](../eigenvalues-and-inverse-problems/SP-08/README.md) | Partially resolved | 2510.15919, proved cases and conclusion. | Retained challenging / community. |
| [SP-09](../eigenvalues-and-inverse-problems/SP-09/README.md) | Partially resolved | 2508.13834v1, Corollary 3.5, Propositions 3.15, 3.21, 4.14. | Retained challenging / specialist. |

Counts: 34 Open, 10 Partially resolved. Six entries have rating changes; all 44 now have explicit status metadata and rating rationales.


## Concurrent additions: SP-10–SP-12

These three entries were added by another task during the audit. They are separate from the original 44-entry count above. Each complete statement was compared with the full cited primary manuscript, its 2026 publication record, and targeted later searches. No general resolution was located; the dates describe a bounded literature check.

| ID | Verdict | Evidence and exact partial boundary | Rating decision |
| --- | --- | --- | --- |
| [SP-10](../eigenvalues-and-inverse-problems/SP-10/README.md) | Partially resolved | Barioli et al., Conjecture 1.1; Jansrang–Narayan (2021), §1 and Theorem 1, record/prove exact GCC cases including trees, chordal graphs and shadow families through the stronger real PSD inequality. | Retained extreme / community. |
| [SP-11](../eigenvalues-and-inverse-problems/SP-11/README.md) | Partially resolved | Barioli et al., paragraph before Conjecture 1.5 and Theorem 2.11. The stronger PSD/SAP witnesses prove the displayed target for explicit girth, degree and forbidden-subgraph regimes. | Retained extreme / community. |
| [SP-12](../eigenvalues-and-inverse-problems/SP-12/README.md) | Partially resolved | Barioli et al., Conjecture 4.1 and preceding clique-minor bound; Chudnovsky–Fradkin (2008), Theorem 1.1, imply the exact target for quasi-line graphs. | **Difficulty extreme → challenging**; retained specialist impact. The implication from Hadwiger supplies a route, not an equivalence or independent extreme-difficulty justification. |

Additional count: 0 Open, 3 Partially resolved; one rating change. All three have normalized status metadata and explicit rating rationales. The weaker all-graph bounds do not establish the partial labels; the proved graph families do. No displayed equations were changed.


## Concurrent additions: IE-24–IE-25 and IV-03–IV-06

These six entries were independently reviewed after initial authorship by the expansion task, separately from the original 44 and the three SP additions. All exact statements and cited locators were checked against primary texts, and every ID received targeted later-resolution searches. The Lee–Min author PDF was retrieved directly after the web reader failed. No new general solution was located.

| ID | Verdict | Evidence and material correction | Rating decision |
| --- | --- | --- | --- |
| [IE-24](../linear-systems-and-elimination/IE-24/README.md) | **Partially resolved → Open** | Lee–Min Definitions 1/4, equation (3), §3 conjecture; Hwang et al. §§2.1/5. Rectangles proved in §5 have corners and are outside the displayed smooth-boundary target. | Retained challenging / community. |
| [IE-25](../linear-systems-and-elimination/IE-25/README.md) | **Partially resolved → Open** | Lee–Min Definition 5 and §4 conjecture; §5 proves RILU, not PMILU. Later MILU preprint explicitly leaves Neumann conditions open. First-pivot exception faithfully preserved. | Retained challenging / community; removed rationale’s unsupported implication of known PMILU domain cases. |
| [IV-03](../intervals-and-absolute-value-equations/IV-03/README.md) | Open | Hladík §9, Conjecture 1; Garloff–Al-Saafin–Adm p.64 before IP4.4 retains the conjecture. An exponential alternative test does not settle this quadratic vertex family. | Retained challenging / specialist. |
| [IV-04](../intervals-and-absolute-value-equations/IV-04/README.md) | **Open → Partially resolved** | Horáček–Hladík–Černý §1.4.3, Theorem9, proves the regular bidiagonal subclass. The chapter assumes bounded solutions; the catalog’s singular/unbounded cases are now explicitly marked as an editorial extension. Hladík §2 leaves general tridiagonal hull computation open. | Retained challenging / community; rationale now matches the flag. |
| [IV-05](../intervals-and-absolute-value-equations/IV-05/README.md) | Open | Hladík §9, question before Theorem25. The theorem only reduces right-hand-side choices; the 2021 recognition result addresses a different task. | Retained challenging / specialist; rationale now matches the flag. |
| [IV-06](../intervals-and-absolute-value-equations/IV-06/README.md) | **Partially resolved → Open** | Hladík–Daney–Tsigaridas JCAM2011 §1 exact conjecture; CAMWA2011 §2 studies a coupled symmetric subset, not the displayed independent-entry family. That adjacent result does not establish the previous partial label. | **Impact community → specialist**; retained challenging difficulty. |

Additional count: 5 Open, 1 Partially resolved; one impact change and four status corrections. No displayed equations were changed. Original 44-entry counts remain unchanged.
