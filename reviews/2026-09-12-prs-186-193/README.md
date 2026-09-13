# Independent audit of PRs 186–193

Reviewed on 12 September 2026 by coordinating and independent Codex AI agents.
These are mathematical, source-fidelity and operational audits, not external
human peer review, authorship adjudication or historical-priority certification.

**All seven contributions pass within their stated scopes.** The integration
preserves each reviewed contribution head, every original mathematical target,
all 217 permanent IDs and canonical paths, and prior-source credits.

| PR | Target | Reviewed head | Disposition |
| --- | --- | --- | --- |
| [186](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/186) | MI-15/16/20/27 | `fc83d2959723c92967a26777e5238404804c848c` | MI-16 becomes Partially resolved; other statuses remain |
| [187](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/187) | MI-03 | `94e8ae24e4c10e79d8b3502101ee4a0287506f81` | Lean verified; complete sharp constant |
| [189](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/189) | TR-14 | `5d79588e225376c81f1a664f3ec128a482bf7103` | Solved affirmatively; all complex Hankel data |
| [190](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/190) | RA-14 | `43754370fadf404837fc2330b9cdf55ffd92fc1c` | Remains Partially resolved |
| [191](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/191) | RA-04 | `e15ce4854d1a9c9fa457b93da78fca04febf200a` | Becomes Partially resolved |
| [192](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/192) | IE-23 | `3fc8bde9c014d22575bbfb73c644c5ce0c492d29` | Lean verified; complete negative answer |
| [193](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/193) | IV-06 | `f73edd6c6562a78d1c4f56fdc4c1c75dac9ace4a` | Lean verified; complete negative answer |

The final catalog has **19 Lean verified, 74 Solved, 51 Open and 73 Partially
resolved entries**: 124 targets still contain open cases. Only TR-14 leaves
the open-target count. No problem is renumbered or replaced.

The [independent integration review](integration-review.md) and
[preservation evidence](integration-preservation.json) confirm exact preservation
of all 1,890 incoming authored paths outside combined indexes, all 6,974 base
paths, the registry, all resolution records, and 80 shared infrastructure paths.

## Mathematical review

- [Matrix partial results](PR186-review.md) and [independent cross-review](PR186-cross-review.md):
  exact SOS certificates in orders 8–12; a permanent formula for the entire
  one-exceptional-eigenvalue class; dual/projective Schatten reductions; and
  variable-trace projection equivalence plus a strictly positive coefficient
  sharpness family. The general MI-15/16 cases and MI-20/27 targets remain open.
- [MI-03](PR187-review.md): genuine principal CFC moduli, Euclidean operator
  norms, the universal positive decomposition and a symbolic all-k
  root-of-unity witness prove the actual least admissible constant and infimum.
- [TR-14 full manuscript](PR189-review.md) and [second exact-rank review](PR189-cross-review.md):
  the Frobenius moment algebra and both symmetric upper bounds match the
  unrestricted ordinary-rank lower bound. The contextual product argument
  proves auxiliary algebras reduced before using finiteness; arbitrary CP
  decompositions and repeated/mixed roots remain covered. The first review
  also checks the later border-rank claims and appendices.
- [RA-14](PR190-review.md): finite-parameter rank and exact-recovery bounds,
  large-rank regime and spectral-to-PCA reduction, retaining the polynomial
  dimension restriction. Other simultaneous parameter regimes stay open.
- [RA-04](PR191-review.md): interpolation/fractional-moment bounds and named
  closed regimes. The general bound still contains the extra t log m term;
  monomial ill-conditioning is not a counterexample to the original target.
- [IE-23](PR192-review.md): actual nonzero-input supremum and complex lp/Euclidean
  norms; two different rational right inverses at p=4 attain the same minimum
  over every complex right inverse, refuting the whole uniqueness assertion.
- [IV-06](PR193-review.md) and [independent cross-review](PR193-cross-review.md):
  the full independent-entry box, four actual eigenpairs, three universally
  excluded separators, and genuine connected-component cardinality refute the
  at-most-dimension bound. Exactly four components is not claimed.

Review includes fresh exact algebra/certificate reconstructions and inspected
supplied-script reruns. The retained scripts and JSON results distinguish
finite tests from the universal analytic proofs. Numerical experiments are
not treated as certificates of the open general cases. Original pre-publication
attachments unavailable in this environment are not independently authenticated
merely from submitted hash manifests; final contributed content was reviewed.

## Verification and publication

[Authenticated upstream evidence](upstream-ci-evidence.json) binds each of the
three new formalizations to its actual successful upstream Linux run and tested
merge parents. All **1,707 tracked project input hashes**, three source locks
and configurations match. All **24 public exports** are accepted by the actual
Comparator and Lean default kernel; **49 transitive axiom reports** use only
`propext`, `Classical.choice` and `Quot.sound`. Actual sandbox, raw-kernel,
Comparator, admitted-proof and native-proof rejection controls passed. No
definition exceptions or local macOS execution are substituted for Linux proof
verification. No Lean claim is made for the informal contributions.

All **77 repository tests** passed on the combined candidate, as recorded in
[the test log](repository-tests.log). Permanent-ID validation, catalog
generation, the 17 dedicated ID tests, math formatting and all three eight-export
manifest checks passed. The generic whitespace scan flags preserved archived
diff/log/CSV formatting and Markdown line breaks; it reports no Lean/Python/TeX
source whitespace issue. Those historical archives were not rewritten.

All relevant canonical and newly supplied manuscript PDF pages were visually
inspected: see [Lean publication review](lean-publication-review.md), the
matrix/RA cross-review and the TR-14 review. No corrective mathematical or PDF
edit was required. Only combined root/category indexes and the retained
resolution narrative required conflict resolution during integration.

This record precedes the final integration workflow. Publication requires all
final integration GitHub checks to pass; the integration PR records their
final run links and outcome.
