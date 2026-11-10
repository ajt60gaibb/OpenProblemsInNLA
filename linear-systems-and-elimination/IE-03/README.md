# IE-03 — Cryer's Hadamard complete-pivoting conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-11-09

## Negative resolution — 2026-10-31

Matias Andia (Princeton University), [*A Hadamard matrix with growth factor
greater than its order*](https://zenodo.org/records/23871097),
**Theorem 1** (page 1; construction and proof in Section 2, pages 1–4),
exhibits a row and column permutation of the Sylvester Hadamard matrix of
order $`n=4096`$ with a valid complete-pivoting path for which

```math
\rho(H)=4608=\frac98\,4096>4096.
```

The matrix is already ordered so that every diagonal pivot is maximal in
absolute value in the active Schur complement. The first pivot exceeding the
order is $`+4608`$ at step $`4089`$. This addresses the exact real-Hadamard,
exact-arithmetic target below: a single admissible path with growth greater
than the order refutes the universal assertion, including its quantification
over all tie choices. **Corollary 1** (Section 3, page 4) extends the example to
every order $`2^d`$ with $`d\ge12`$. The manuscript's separate asymptotic
Conjecture 1 remains a conjecture; no smallest-counterexample claim is made.

The [submission package](../../references/andia-ie03-2026-10-31/README.md)
contains the manuscript source, explicit matrix, two supplied verification
scripts, and [fresh computational reproduction records](../../references/andia-ie03-2026-10-31/verification/README.md).
Codex reran the construction and dense checks during PR preparation. The
catalog initially recorded the result as **Solution claimed**. In the
manuscript's acknowledgements, Matias Andia credits GPT-6 Astra Pro with
finding the counterexample.

## Lean proof and verification evidence

**Lean verified — 9 November 2026.** OpenAI Codex formalized the result
using Lean 4.33.1 and Mathlib revision `0df444a`.
The declaration `NLA.IE03.counterexample` constructs a real order-4096 matrix
with sign entries, the Hadamard Gram identity, and a legal complete-pivoting
path of exact growth 4608. The declaration `NLA.IE03.cryer_false` negates
the original assertion over all positive orders, real Hadamard
matrices, and admissible paths. The formalization checks all 124 local pivots
and Schur updates and proves the four lifts that extend them to the full
4096-step path. [Immutable proof revision](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/89987eb5059ce5a497c18ce50c9b86f8cf394b86/linear-systems-and-elimination/IE-03/lean)
· [Pinned Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).

Two independent AI-agent reviews approved the exact statement before proof
development. Three further reports approved the proof's fidelity,
correctness, and reuse and attribution. The isolated Linux run passed
Comparator, Lean's default kernel, and the sandbox and rejection controls
for the reviewed proof sources. Both exports depend on `propext`,
`Classical.choice`, and `Quot.sound`. [Reproduction and reviews](lean/README.md)
· [Retained Linux evidence](lean/verification/linux-2026-11-09/README.md)
· [Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/42710286364).

The original ID, mathematical target, and earlier status checks are retained.
The difficulty, importance, and rating rationale are historical assessments
of the original open target.

**Rating rationale:** Extreme reflects a longstanding conjecture across every Hadamard order and pivot path; community impact comes from sharp complete-pivoting stability and its connection to Hadamard structure.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $`\|A\|_{\max}=\max_{ij}|a_{ij}|`$. A pivoting path creates successive active Schur complements $`S_1=A,S_2,\ldots,S_n`$, with row/column permutations as appropriate. Its element-growth factor is

```math
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
```

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

A real Hadamard matrix of order $`n`$ is a matrix $`H\in\{-1,1\}^{n\times n}`$ satisfying $`HH^T=nI`$. Prove or disprove that, for every Hadamard matrix and every complete-pivoting path,

```math
\rho(H)=n.
```

The quantified input is an existing Hadamard matrix; this question does not ask whether Hadamard matrices exist in every order divisible by four. Since $`\|H\|_{\max}=1`$, the requested upper bound says that no entry in any active Schur complement can exceed $`n`$ in absolute value. The final pivot already supplies the matching lower bound. Permuting or resigning rows and columns does not remove the need to account for all allowed pivot paths.

## References

N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*,
2nd ed.](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.17,
p. 193, poses this book-sourced question. Kravvaritis and Mitrouli, [*The growth factor of a Hadamard matrix of order 16 is 16*](https://doi.org/10.1002/nla.637), NLA with Applications 16 (2009), 715–743, introduction and main result. Peca-Medlin, [*Complete pivoting growth of butterfly matrices and butterfly Hadamard matrices*](https://doi.org/10.1080/03081087.2026.2660796), 2026, introduction and §2.

## Earlier status check — 2026-09-08

Searches for `Hadamard Cryer 2026` and `Hadamard growth conjecture 2026 proof` found the general conjecture still identified as open in the 2026 butterfly paper. Shah–Urschel's August 2026 general elimination construction is not a Hadamard counterexample. Known Sylvester and small-order cases must not be counted as additional open problems.

## Audit update — 2026-09-10

The [2026 butterfly paper](https://www.tandfonline.com/doi/abs/10.1080/03081087.2026.2660796), §3, retains the general Hadamard conjecture while recording proofs for Sylvester-type matrices in all their orders and every Hadamard matrix of order at most 16. Hence the status now records partial resolution. Searches for Cryer/Hadamard growth and later complete-pivoting results found no general proof or counterexample; asymptotic bounds for unrestricted matrices do not settle this subclass.

**Clarification — 2026-10-31:** The preceding paragraph records the earlier
audit, not the current status. Its reference to Sylvester-type matrices must
not be read as a bound for every admissible pivot path on every permutation:
the submitted counterexample is itself a permuted Sylvester matrix. The
current claim and its verification level are described above.
