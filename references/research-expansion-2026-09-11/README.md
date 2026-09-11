# Fourteen literature additions — September 11, 2026

[Catalog](../../CATALOG.md) · [Sources and status checks](../README.md)

This search adds **14 canonical entries**: three Open, ten Partially resolved,
and one retained **Solved (refuted)** entry. RA-20's proposed universal formula
was disproved during independent review; its original statement and ID remain.
The additions increase the open-target count by 13. Current aggregate totals
are given in the generated catalog and include the latest resolutions on main.
All 203 previously registered ID/path pairs and existing problem statements
remain unchanged. Related parameter cases and equivalent formulations are grouped.

## Admissions

Each linked page supplies a self-contained statement, primary-source links,
known cases, numerical significance, ratings and a dated search for subsequent
proofs or counterexamples. Each also has standalone LaTeX and PDF exports.

| ID | Target | Primary locator and surviving question |
| --- | --- | --- |
| [IE-26](../../linear-systems-and-elimination/IE-26/README.md) | Austin–Trefethen perturbed Fourier stability | SINUM 55 (2017), pp.2115–2116 and 2119; infinity- and two-norm bounds grouped. August 2026 two-norm progress retains a logarithmic factor. |
| [IE-27](../../linear-systems-and-elimination/IE-27/README.md) | Radau stage-preconditioner spectral disk | Axelsson–Dravins–Neytcheva, NLAA 31 (2024), Conjecture 1; symmetric elliptic setting stated explicitly. Two stages are known. |
| [IE-28](../../linear-systems-and-elimination/IE-28/README.md) | Positive diagonal collocation preconditioning with nilpotent stiff limit | Van der Houwen–de Swart, SISC 18 (1997), §3.2.1, p.46; arbitrary positive distinct nodes formalized explicitly. SISC 47 (2025), §2.2.3, retains the existence question. The page includes an elementary two-stage verification. |
| [SP-13](../../eigenvalues-and-inverse-problems/SP-13/README.md) | Trace-norm-small perturbations preserve Hermitian spectral distributions | Barbarino–Serra-Capizzano, NLAA 27 (2020), Conjecture 1, §6; remove the uniform perturbation bound. The 2025 normal-sequence theorem does not settle this. |
| [SP-14](../../eigenvalues-and-inverse-problems/SP-14/README.md) | Widom's canonical Toeplitz eigenvalue distribution conjecture | Bogoya–Böttcher–Grudsky (2012), §1 after (1.1), restates Widom (1990); Bogoya et al., NLAA 31 (2024), introduction before Theorem 1, reaffirms it. |
| [SP-15](../../eigenvalues-and-inverse-problems/SP-15/README.md) | Uniform finiteness of unitary classes with prescribed shifted singular values | Fortier Bourque–Ransford (2009), Theorem 1.4 and §6.2; Ransford (2010), Theorem 5.4 and discussion. Exceptional data fibers remain the target. |
| [MF-23](../../matrix-functions-and-stability/MF-23/README.md) | Complete Crouzeix conjecture | Crouzeix (2007); Åhag–Czyż–Virtanen, arXiv:2608.27346v3, September 9, 2026, equation (1.2). The complete matrix-valued target survives the recent scalar proof claims. |
| [MF-24](../../matrix-functions-and-stability/MF-24/README.md) | Dimension-independent polynomial norm comparison from super-identical pseudospectra | Fortier Bourque–Ransford (2009), p.513 after Theorem 1.3; Ransford–Walsh, arXiv:2109.14472v2, Theorem 1.3 and Proposition 5.1, improve dimension-dependent constants. |
| [RA-19](../../randomized-and-low-rank-approximation/RA-19/README.md) | Critical-point count for corank-one approximation with one fixed zero | Kubjas–Sodomaco–Tsigaridas, LAA 641 (2022), Conjecture 5.1 and Table 2; manuscript p.19. The nontrivial range is explicitly restricted to dimensions at least three. |
| [RA-20](../../randomized-and-low-rank-approximation/RA-20/README.md) | Critical-point counts for symmetric rank-two approximation with diagonal zeros | Same paper, Conjecture 5.6 and Table 7; manuscript p.21. Four formulas and their original range are retained. The exact n=s=3 counterexample gives three critical points, not four; the joint conjecture is refuted. |
| [MI-30](../../matrix-inequalities-and-norms/MI-30/README.md) | Product inequality for disjoint Wishart principal minors | Genest–Ouimet–Richards, EJP 29 (2024), Conjecture 1.1, equation (6); arbitrary determinant blocks and nonnegative real powers. The two-block case is known. |
| [MI-31](../../matrix-inequalities-and-norms/MI-31/README.md) | Sharp parameter dependence for structured Gaussian operator norms | Latała–Strzelecka, Advances in Mathematics 501 (2026), Conjecture 5. The absolute constant remains conjectural after their proof of the older fixed-exponent comparison. |
| [MI-32](../../matrix-inequalities-and-norms/MI-32/README.md) | Spectral norms of independent entries with regular moment growth | Latała–Świątkowski, EJP 27 (2022), Conjecture 4.3; includes weighted-sign Conjecture 1.2. Later bounds retain iterated logarithms. |
| [FR-12](../../frames-and-matrix-designs/FR-12/README.md) | Counting labeled real Hadamard matrices | Ferber–Jain–Zhao, CPC 31 (2022), published Conjecture 1.3, p.456; distinct from Hadamard existence and pivot-growth questions. Reaffirmed in 2024 and 2026 sources. |

## Scope and source corrections

The search followed the requested authors into subsequent literature. In
particular, the Austin–Trefethen conjectures supply a direct named-author
addition. Existing screens already cover many Golub, Stewart, Demmel and
Higham leads. Searches around Bartlett did not establish a new attributable
conjecture; adjacent random-matrix results are credited to their actual authors.

The two zero-pattern entries disclose small-dimensional failures in the
unqualified printed formulas. Further independent review found that RA-20
also fails at the admissible case n=s=3: the hollow symmetric determinant is
2abc, whose three smooth coordinate-plane components each contribute one
generic critical point. [The complete negative resolution and exact checks](ra20-resolution/README.md)
replace the initial Open classification. The original target and permanent ID
are retained without narrowing the dimension range. The other formulas and
remaining dimensions are not claimed resolved separately. RA-19 remains Open.
The nonsymmetric rectangular formula in the source has a table/label discrepancy
and was withheld.

IE-27 follows the original conjecture's **radius**, correcting a later
restatement's word “diameter,” and explicitly uses the symmetric elliptic
setting of the later analysis. IE-28 excludes a zero collocation node, which
would force an eigenvalue one in the proposed nilpotent matrix. The formula
for its two-stage case was independently checked from trace and determinant.
MF-23 distinguishes the complete conjecture from scalar claims; its recent
three-dimensional result is labeled a preprint claim. SP-15 and MF-24 have
older source statements: their status evidence is a bounded later-literature
search, not a recent explicit reaffirmation.

## Exclusions and research records

- [Krylov, conditioning and elimination](krylov-candidates.md): LOPCG rate
  quantifiers, previously reserved extended-Krylov bounds, and later block
  Gram–Schmidt results.
- [Matrix functions and pseudospectra](functions-candidates.md): source checks
  for the admitted targets and the uncounted complete abstract COR extension.
- [Random matrices and structured approximation](randomized-candidates.md):
  Wishart/scalar-GPI distinction, corrected published Hadamard count,
  unresolved sparse-matrix notation, and recent solution claims that prevent
  recycling historical embedding, ellipsoid-fitting and normal-matrix counts.
- [Structured spectral distributions](structured-candidates.md): equivalence
  and source checks for SP-13/SP-14, resolved ALIF claims, and held rank-increment
  statements.

The review compared the displayed formulas, fields, normalization and
quantifiers against primary statements, then searched current versions,
later papers and proof/counterexample combinations through September 11,
2026. Multiple readers independently checked the statements and borderline
cases. This establishes an auditable admission basis, not an exhaustive
certification that no solution exists.

## Repository checks

The permanent-ID validator was run against `origin/main` before index
generation, and all 17 numbering-safeguard tests passed. The 14 LaTeX/PDF
exports were rebuilt and their pages inspected. Page-break adjustments in
the existing renderer keep reference lists and status notes together.
Previously published canonical pages and exports were not modified. The RA-20 resolution, IE-27 section locator, and SP-15 reference were corrected during review, and their affected exports were rebuilt.
