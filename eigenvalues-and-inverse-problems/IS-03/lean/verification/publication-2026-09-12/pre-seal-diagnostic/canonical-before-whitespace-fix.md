# IS-03 — Johnson's derivative-realizability conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified  
**Last checked:** 2026-09-12  

**Rating rationale:** Challenging reflects preserving nonnegative realizability under polynomial differentiation; community impact connects the nonnegative inverse eigenvalue problem with polynomial critical points.

## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](solution.md) · [PDF](solution.pdf) · [LaTeX](solution.tex). **Theorem 1 and equations (1)–(7).**

The nonnegative real order-seven matrix $`A=\mathop{\mathrm{diag}}\nolimits(1/2,C_2,C_4)`$ has a normalized characteristic-polynomial derivative whose seventh power sum is $`-8593/823543<0`$. Every power of a nonnegative matrix has nonnegative trace, so the derivative cannot be realized at order six, or after any zero padding. Reducibility and positive trace are allowed in the original target. This refutes its universal assertion.

The complete argument received an independent Codex-agent **PASS** on 11 September 2026. The [review report](../../references/colbrook-additional-2026-09-11/verification/reviews/IS-03-review.md) records the exact scope and a hash of the original reviewed manuscript. The mathematical sections remain unchanged in the authored version. Original ChatGPT generation is disclosed; that dated agent review was informal. The later Lean verification is documented below; external human peer review is not claimed. [Submission and verification record](../../references/colbrook-additional-2026-09-11/README.md).

The original statement, source references and prior audit notes are retained; the former difficulty rating is historical.

## Lean proof and verification evidence - 2026-09-12

**The complete original derivative-realizability conjecture is Lean verified with a negative answer.** The [proof at revision f87375f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean) proves that the unchanged nonnegative order-seven source matrix has no entrywise-nonnegative realization of its normalized characteristic-polynomial derivative at order six. The full original quantifiers and exact order $`n-1`$ are retained. Neither symmetry nor diagonalizability is assumed; entrywise nonnegativity is not replaced by positive semidefiniteness.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains mathematical counterexample authorship. Johnson and Hoover, McCormick, Paparella and Thrall retain the original conjecture and source attribution.

The seven [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean/Solution.lean), each with prefix `NLA.IS03.`, are:

- `nonnegative_power_trace`: every natural power of an entrywise-nonnegative real matrix has nonnegative entries and trace, including order and power zero.
- `witness_admissible`: the actual source matrix is entrywise nonnegative and has trace $`1/2`$.
- `witness_polynomials`: its genuine characteristic polynomial and normalized derivative have the stated coefficients; the derivative is monic of degree six.
- `trace_moment_certificate`: every real order-six matrix with that characteristic polynomial has all seven prescribed power traces, without a spectral assumption.
- `negative_moment`: the seventh value is exactly $`-8593/823543`$ and strictly negative.
- `counterexample`: the admissible source matrix has no nonnegative order-six realization of its actual normalized derivative.
- `not_derivativeRealizabilityConjecture`: negation of the complete original universal assertion.

Two independent statement approvals preceded implementation; two independent final proof referees approved the frozen proof after fresh source elaboration, actual-term inspection and replay of the retained numerical checker. [Ubuntu run 34728101436](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436) matched all seven exports with the sandboxed Comparator, replayed the solution in Lean's default kernel and passed both actual isolation/rejection-control suites. The [operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind all 303 submitted inputs; [root acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) independently checked their identity and actual execution. All 18 internal/public transitive axiom reports allow only `propext`, `Classical.choice` and `Quot.sound`. Operational and publication roles do not add mathematical referees. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The material explicit kernel LeanCert certificate proves the singleton sign $`-8593/823543<0`$. Exact characteristic-polynomial, spectral, Vieta/Newton and trace arguments connect that sign to the full contradiction. Separability and an actual eigenbasis of any potential realization are derived, not assumed. No approximate roots, numerical eigensolver or interval subdivision is used. The source's stronger zero-padding exclusion and its separate Monov consequence are outside these seven exports. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml), [reviews](lean/reviews/) and [pins](lean/lake-manifest.json).

From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  eigenvalues-and-inverse-problems/IS-03/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

For every integer $`n\geq5`$ and every real entrywise-nonnegative matrix
$`A\in\mathbb R^{n\times n}`$, define $`p_A(z)=\det(zI-A)`$.
Must there exist an entrywise-nonnegative
$`B\in\mathbb R^{(n-1)\times(n-1)}`$ such that

```math
\det(zI-B)=\frac1n p_A'(z)\qquad\text{as polynomials in }z?
```

Equivalently, the critical points of the characteristic polynomial, counted
with multiplicity, would themselves form a realizable spectrum of the smaller
order. Neither $`A`$ nor $`B`$ is assumed symmetric or diagonalizable. The
realization must have exactly order $`n-1`$; allowing arbitrary additional zero
eigenvalues changes the problem. This would provide a dimension-reduction
operation for nonnegative spectral realization.

## References

Hoover, McCormick, Paparella, and Thrall,
[*On the realizability of the critical points of a realizable list*](https://arxiv.org/pdf/1712.05454),
Conjecture 1.2, p. 2, and §6. The paper credits the conjecture to Johnson and
records the Cronin–Laffey low-order results.

## Earlier status check — 2026-09-08

Searches for `Johnson conjecture derivative nonnegative
matrix characteristic polynomial proof counterexample`, `1712.05454 2026`,
and `Monov conjecture solved` found no general resolution. The source proves
several classes and records the solved cases $`n\leq4`$, and
$`n\leq6`$ with $`\mathop{\mathrm{tr}}\nolimits A=0`$. Nonnegative power sums alone are a
different hypothesis. Monov's weaker moment conjecture is not separately
counted here.

## Audit update — 2026-09-10

Rechecked the [primary manuscript](https://arxiv.org/pdf/1712.05454), Conjecture 1.2 and its proved families; the [journal version](https://doi.org/10.1016/j.laa.2018.06.024) is LAA 555 (2018), 301–313. Results for Ciarlet/Suleĭmanova lists, appropriate companion-matrix realizations, and trace-zero lists of orders five and six settle substantive portions of the displayed target. Johnson-conjecture/critical-point searches found no general proof or counterexample.
