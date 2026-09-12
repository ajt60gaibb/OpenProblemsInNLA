# Maintainer audit of nine solution submissions — 12 September 2026

Nine submissions passed independent mathematical review by the repository's Codex audit agents. The reviewers read the complete proofs, compared them with the original canonical targets, checked the necessary primary sources, and inspected all 71 submitted problem and solution PDF pages. Submitted review labels and finite numerical checks were not treated as substitutes for the proofs.

These are informal AI-agent audits. They support **Solved** under the repository policy; they do not establish Lean verification, external human peer review, or historical priority. The submitted attribution and AI-assistance disclosures remain intact.

| PR | Target | Audited head | Review |
| --- | --- | --- | --- |
| [132](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/132) | RA-19: critical-point count | `b7be90345ad9aba7f420c90f2ea407b5b0182243` | [PASS](PR132.md) |
| [134](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/134) | SP-13: Hermitian spectral distributions | `daf8f999e50ad1d3cb04805a3d53cc3fed85808e` | [PASS](PR134.md) |
| [136](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/136) | SP-15: shifted singular-value fibers | `9139b771791820c62a3f11d1f7394f25f986609a` | [PASS](PR136.md) |
| [138](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/138) | MF-02: uniform asymptotic cubic overhead | `f606d90ed0dc35172638cd41f6f0a246044c9f18` | [PASS](PR138.md) |
| [140](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/140) | IE-26: both Fourier stability bounds | `fe894049e88c8a88baaeddbff9ca5c187ffff4be` | [PASS](PR140.md), [additional cross-check](PR140-crosscheck.md) |
| [143](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/143) | KE-05: spectrum-uniform interpolation | `dcd362b46b0c20a9ca5f38c9ab35138c452a65ee` | [PASS](PR143.md) |
| [145](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/145) | MF-21: higher-order Toeplitz threshold | `eb37bc17a462177f57efa270e9a9f9b17e9d88e2` | [PASS](PR145.md) |
| [147](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/147) | FR-12: labeled Hadamard counting | `70929e8401ab454179c9d3fcfb1b8c042e337a33` | [PASS](PR147.md) |
| [149](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/149) | MF-06: pointwise lower-Lipschitz continuity | `db5301fbaa88f43bc537f2e6cae32dc7e7581530` | [PASS](PR149.md) |

The complete original targets and all submitted proof artifacts are retained. Reports preserve their original working-directory references; the immutable reviewed commits identify the authoritative submitted materials. The mathematical audits began against published main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. Integration also retains subsequent published main `7a149f0fbd80a24404c249170d31d88542125b4c`, including the separately audited PRs #93 and #130.

Integration resolves competing catalog updates by regenerating the indexes from the canonical pages, retains every resolution notice, and combines the problem-specific PDF layout settings. All 217 ID/path pairs remain unchanged. The resulting counts are 58 Open, 71 Partially resolved, 87 Solved, and one Lean verified.

Local validation passed against published main: the permanent-ID validator, catalog generation, all 17 permanent-ID tests, and all three status/count tests. The merged renderer files parse successfully. Publication additionally requires the unchanged GitHub permanent-ID workflow to pass for the final integration commit. PR #141's separate Lean-verification audit is outside this batch.
