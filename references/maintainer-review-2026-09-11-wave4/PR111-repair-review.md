# PR 111 final repair review

**Verdict: PASS. No mathematical or artifact blocker remains in this bounded repair review.**

Reviewed 2026-09-11 by an independent Codex agent. Original PR head: `450ee69e20e54bb687240e01477cf95b0de61e0e`. Repaired checkout at review time: commit `12341b023f95682c44c893bb30c1c3ee4947ef9c`, plus the final RA-20 forced-page-break removal and regenerated RA-20 problem TeX/PDF. The exact reviewed source and artifact hashes are in `PR111-repair-final-hashes.json`. The reviewer made no changes to the source worktree.

## Permanent target and resolution

The entire original RA-20 `## Statement` section, including the heading, range, smooth-locus definition, full-Frobenius metric, four formulas and grouping sentence, is byte-identical to `origin/pr/111`. Its SHA256 is `f20a1a0f0b62950dcd15a1a199ce2f0da10569f31e5bb9a931d06d3afd6648a3`. The permanent ID and canonical path remain.

The complete proof in `randomized-and-low-rank-approximation/RA-20/solution.md` is sound. For n=s=3, the constrained variety is the reduced hypersurface abc=0, a union of three coordinate planes. A point is smooth precisely when exactly one coordinate is zero. For generic data with three nonzero off-diagonal coordinates, orthogonal projection to each plane supplies exactly one critical point in this smooth locus. These three points exhaust the smooth locus, are distinct, and each has restricted Hessian 4I_2. Thus the generic complex count, including multiplicity, is three. The original conjectural formula gives four.

This refutes the original grouped universal assertion without narrowing or replacing its target. The Solved/refuted label and README, RESOLVED, research-record descriptions correctly refrain from settling the remaining individual formulas or larger dimensions. Matrix-rank-two points on the coordinate axes are correctly excluded as singular points of this constrained variety. The conclusion is generic, not an inference from one numerical witness.

Read the exact checker before executing it; it has no writes or network calls. Its recorded rational output is reproduced: critical triples (0,2,3), (1,0,3), (1,2,0), determinant gradients (12,0,0), (0,6,0), (0,0,4), restricted Hessian determinant 16, squared distances 16,22,32. Independently rederived the determinant and tangent conditions and checked 64 rational generic data triples, with three distinct smooth critical points in each. The proof, rather than sampling, establishes exhaustion for generic complex data. Results: `PR111-repair-exact-checks.json`.

Primary source checked: Kubjas–Sodomaco–Tsigaridas, [arXiv:2010.15636v2](https://arxiv.org/pdf/2010.15636v2), printed p.21, Conjecture 5.6 and Table 7. Both display four at n=s=3. Section 2 uses the smooth-locus, complex-bilinear ED-degree convention; its Lemma 2.2 on additivity across components is consistent with the direct proof. No diagnosis of the source's computation or novelty claim is needed or made.

## Citation and record repairs

- IE-27 README and regenerated TeX/PDF now correctly cite §5.1, Conjecture 1, equations (17)–(18), and Theorem 1 of [Axelsson–Dravins–Neytcheva](https://www.diva-portal.org/smash/get/diva2:1740890/FULLTEXT01.pdf). The original paper's section heading and conjecture were checked in the preceding eight-entry source audit.
- SP-15 README and regenerated TeX/PDF now explicitly cite Ransford–Walsh, [arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), 9 July 2022, Theorems 1.3–1.4. Those polynomial-norm comparison and similarity-conditioning results do not imply finiteness of unitary similarity classes. The old unsupported reference to estimates “below” is removed.
- `RESOLVED.md`, the final research admission record and the historical randomized-candidate correction consistently record the precise negative result and preserve the original statement. All fourteen new entry statuses were independently counted: three Open, ten Partially resolved, one Solved, hence thirteen contribute to the open-target count.
- A stale script/output filename in the independent reconstruction was reported and corrected: it now names the actual `verify_counterexample.py` and `exact-results.json` files.

## PDF QA

Used the PDF skill for read-only rendering and inspection. All four final PDFs were rendered to PNG under `pr111-repair-pdf-qa/`, all seven final pages visually inspected, and extracted text compared with the repaired Markdown/TeX. The superseded three-page RA-20 problem export had an obsolete forced break; this was reported, fixed by the integrating agent and re-rendered. The final two-page version was re-inspected. All mathematical displays, source locators, status descriptions and the complete proof are present and legible. No clipping, overlap, missing glyphs or material source/export inconsistency was found. SP-15 has a short continuation on page 2; its content remains complete and readable.

| Artifact | Pages | Final SHA256 |
| --- | ---: | --- |
| RA-20/problem.pdf | 2 | `7fdfd0e9874863eabead0a38d2245afedf4b81c64d56c9eddd30e7a02a805c47` |
| RA-20/solution.pdf | 1 | `335f325c03c9c1bd9a4ec0490699ae43296b58e023ed12e0962761dab37b17de` |
| IE-27/problem.pdf | 2 | `1dc4510c98abf761c2e5ae65653d9a1f8d594924605a58fe592712311271f474` |
| SP-15/problem.pdf | 2 | `d30cf92bdc9df05eff61e364c9a7d26fafee32d23dff196141607d5931faf868` |

The renderer adjustment only removes RA-20 from the fixed reference-page-break set. The optional solution-template email conditional suppresses an empty mailto link and does not affect the proof. Repository-wide CI and final merge-head verification remain the integrating agent's responsibility. This review supplements `PR-111-eight-entry-review.md`; it is automated-agent review, not formal verification or external human peer review.
