# Primary sources and proof inputs

The manuscript was prepared against the PF-04 statement and the publicly available primary sources below. Third-party papers are referenced, not redistributed.

## PF-04 target

**OpenProblemsInNLA, PF-04: The maximum cp-rank in order six.** The entry's stated last-check date is 2026-09-10. Its requested conclusion is a real exact nonnegative 6-by-9 factor for every order-six completely positive matrix, allowing zero columns.

```text
https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/nonnegative-and-positive-factorizations/PF-04
https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/nonnegative-and-positive-factorizations/PF-04/README.md
```

The catalogue's existing exceptional-boundary reduction is not treated as a proof for arbitrary zero-entry matrices.

## K1: Order-five maximum

Naomi Shaked-Monderer, Immanuel M. Bomze, Florian Jarre, and Werner Schachinger, **On the cp-rank and minimal cp factorizations of a completely positive matrix**, SIAM Journal on Matrix Analysis and Applications 34(2) (2013), 355–368. DOI: 10.1137/120885759.

The publisher's abstract explicitly states that the maximal cp-rank in order five is six. The manuscript uses this bound to dispose of a vertex of degree at most two.

```text
https://epubs.siam.org/doi/10.1137/120885759
```

## K2: Graph bounds

Naomi Shaked-Monderer, **Bounding the cp-rank by graph parameters**, Electronic Journal of Linear Algebra 28 (2015), 99–116. Proposition 2.4, printed page 103 (PDF page 5), gives the connected triangle-free tree and non-tree cases.

Only upper bounds are needed: maximum-degree-two support gives cp-rank at most the number of vertices, and K₃,₃ gives at most nine. Small components are covered separately by the manuscript's elementary order-three proof.

```text
https://emis.de/ft/34721
```

**Care with formulations:** The proof does not use the overbroad equality “cpr(A) = max(n, |E(G)|)” for all triangle-free realizations, since singular trees make such an equality inappropriate. The directly inspected tree/non-tree formulation is sufficient.

## K3 and K4: Exceptional-boundary bounds

Naomi Shaked-Monderer, **On the DJL conjecture for order 6**, Operators and Matrices 11 (2017), 71–88; corrected arXiv:1501.02426v3, submitted 1 June 2017.

**Theorem 1.1** is the nine-column bound under orthogonality to an exceptional extremal copositive matrix. **Lemma 3.1** gives at most seven when that normal has a zero diagonal entry.

```text
https://arxiv.org/html/1501.02426v3
https://arxiv.org/abs/1501.02426
```

The version identifier and submission date, not an HTML-rendering date, identify the cited correction. The proof uses v3 and does not claim the earlier boundary result itself resolved all of PF-04.

## Copositive completion: attribution and an included proof

Leslie Hogben, Charles R. Johnson, and Robert Reams, **The copositive completion problem**, Linear Algebra and its Applications 408 (2005), 207–211. DOI: 10.1016/j.laa.2005.06.019.

Every partially specified copositive matrix with all diagonal entries specified admits a copositive completion. The manuscript includes an elementary proof of the exact version it needs, with unspecified entries set to geometric means of the diagonal entries. It is not presented as a new completion theorem.

```text
https://doi.org/10.1016/j.laa.2005.06.019
https://www.sciencedirect.com/science/article/pii/S0024379505003149
```

## Validation provenance

The mathematical argument beyond the listed published inputs is contained in the manuscript. Enumeration results and exact example calculations come from the included `verification/verify.py`, with output in `verification/results.json`. These computational results are not attributed to the external papers and are not a substitute for review of the analytic proof.
