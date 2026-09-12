# FR-12 — Counting real Hadamard matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Enumeration of orthogonal sign matrices  
**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** Known general upper bounds still have a quadratic exponent, while the conjecture asks for an exponent of order $`n\log n`$. The question concerns the abundance of exact flat orthogonal transforms, with connections to structured matrix constructions and elimination.

## Negative resolution - 2026-09-12

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**The counting conjecture is false.** The [complete proof](solution.md), Lemma 1 and Theorem 1, constructs an injection from two labeled order-$`m`$ Hadamard matrices and a perfect matching of $`2m`$ row labels. It gives

```math
H(2m)\ge(2m-1)!!\,H(m)^2,
\qquad
H(2^k)\ge 2^{\,2^k(k-1)(k-2)/8}\quad(k\ge2).
```

The resulting exponent has order $`n(\log n)^2`$ along powers of two, contradicting every bound $`2^{C n\log_2 n}`$ with fixed $`C`$. [Proof PDF](solution.pdf) · [Standalone proof TeX](solution.tex).

The full argument passed a separate [independent Codex-agent mathematical and source-scope review](../../references/stepaniants-fr12-2026-09-12/REVIEW.md). The [submission record](../../references/stepaniants-fr12-2026-09-12/README.md) preserves the supplied source, exact checks, document conversion and bounded public fork/branch/PR and literature search. Substantial AI assistance is disclosed. That review was informal and did not assert external human peer review or formal verification; the later Lean verification is documented below.

Ferber, Jain and Zhao retain attribution for the conjecture and prior upper bound. This result does not settle existence at every admissible order or determine a matching upper bound for the count. The original statement and historical context below are retained; the difficulty and importance ratings are historical.

## Lean proof and verification evidence - 2026-09-12

**The complete original counting conjecture has a Lean-verified negative answer.** The [proof at revision 3e20bae](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean) counts actual labeled real Hadamard matrices, proves the count finite, and refutes every proposed positive real constant. **Mathematical proof and Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with substantial AI-agent assistance.

The formal construction uses top-to-bottom pairings indexed by a permutation and proves

```math
m!\,H(m)^2\le H(2m)\qquad(m\ge1).
```

This smaller family yields the identical quantitative power-of-two lower bound above and the full original negation. **The stronger informal factor $`(2m-1)!!`$ is outside the Lean exports.** The formal count has no quotient, normalization or assumed family size; in positive dimension its matrix predicate is proved equivalent to Mathlib's `Matrix.IsHadamard`.

The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3e20bae9a07b1a33db8fdfb18bdebb9e590071a9/frames-and-matrix-designs/FR-12/lean/Solution.lean), each with prefix `NLA.FR12.`, are:

- `counting_semantics`: genuine finite counting and the Mathlib Hadamard bridge.
- `injective_doubling`: every constructed output is Hadamard and the map is injective.
- `factorial_doubling`: the cardinality recurrence for every positive order.
- `power_two_nonempty`: existence at every power of two, including order one.
- `power_two_lower_bound`: the exact source lower bound at every $`K\ge2`$.
- `counterexample`: a strict violation for every positive real proposed constant.
- `not_countingConjecture`: negation of the complete original universal assertion.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34718277411](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34718277411) matched all seven exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) bind all 137 input files and both actual isolation/rejection-control suites. All 14 [internal/public transitive axiom checks](lean/verification/linux-2026-09-12/axiom-verification.json) use only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews; external human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits the exact proof's kernel trust; there is **no numerical interval certificate**. Symbolic injection and direct exponential induction avoid large enumerations or approximate logarithms. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  frames-and-matrix-designs/FR-12/lean \
  /absolute/path/to/nla-lean-tools
```

## Statement

For each positive integer $`n`$, let

```math
H(n)=\#\{A\in\{-1,1\}^{n\times n}:AA^{\mathsf T}=nI_n\}.
```

**Conjecture.** There is an absolute constant $`C>0`$ such that

```math
H(n)\le 2^{C n\log_2 n}
```

for every positive integer $`n`$ divisible by four.

The count is of individual matrices with their row and column labels. Matrices related by signed permutations are not identified. The statement does not require that a Hadamard matrix exist at every such order.

## Known bounds and numerical significance

Ferber, Jain and Zhao prove that some absolute $`c_H>0`$ gives
$`H(n)\le 2^{(1-c_H)n^2/2}`$ for every sufficiently large multiple of four.
Whenever $`H(n)>0`$, distinct row permutations of one Hadamard matrix give
$`H(n)\ge n!`$. Thus the conjectured exponent has the smallest possible order
along orders admitting such matrices.

Dividing a Hadamard matrix by $`\sqrt n`$ produces an orthogonal transformation
whose entries all have the same magnitude. The enumeration asks how many
exact sign designs can underlie these transforms. Peca-Medlin's work connects
Hadamard enumeration for butterfly constructions to structured orthogonal
matrices and Gaussian elimination. This is distinct from the Hadamard
existence conjecture and from bounds on elimination growth for a given matrix.

## References and status check

- A. Ferber, V. Jain and Y. Zhao, *On the number of Hadamard matrices via anti-concentration*, Combinatorics, Probability and Computing 31 (2022), 455–477. [DOI](https://doi.org/10.1017/S0963548321000377); [published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/887EFBBF79B804BCDD942029283D4CD7/S0963548321000377a.pdf/on_the_number_of_hadamard_matrices_via_anticoncentration.pdf). Conjecture 1.3 on p.456 is the displayed target; Theorem 1.2 gives the upper bound. The [arXiv record](https://arxiv.org/abs/1808.07222) also supplies the earlier manuscript, where the conjecture has different numbering.
- [BIRS workshop 24w5204 report (2024)](https://www.birs.ca/workshops/2024/24w5204/report24w5204.pdf), Conjecture 28, restates the enumeration target.
- J. Peca-Medlin, *Complete pivoting growth of butterfly matrices and butterfly Hadamard matrices* (2026). [DOI](https://doi.org/10.1080/03081087.2026.2660796), §3 before Proposition 3.1, discusses the general count as conjectural and enumerates specific butterfly constructions.

On 2026-09-11, checked the published statement and later restatements, and
searched the exact title, the authors' names, Hadamard enumeration, upper
bounds, and 2025–2026 proof/counterexample combinations. No full resolution
was located. The butterfly counts apply to restricted families and do not
settle this all-matrix upper bound. This is a bounded literature check.
