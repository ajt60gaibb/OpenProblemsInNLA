# MI-06 — Thompson-type domination for the arithmetic symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified

**Last checked:** 2026-09-12

**Rating rationale:** The arithmetic modulus lacks the useful order structure of the quadratic modulus; a solution would advance a focused family of operator triangle estimates.

## Lean proof and verification evidence — 2026-09-12

**The original MI-06 assertion with factor $`\sqrt2`$ is false, with a complete Lean-verified counterexample.** At the rational pair

```math
A=\begin{pmatrix}1&3/4&0\\0&0&0\\0&0&0\end{pmatrix},\qquad
B=\begin{pmatrix}-1&0&0\\0&0&0\\-3/4&0&0\end{pmatrix},
```

all six genuine matrix moduli are proved exactly. For every complex unitary pair, a nonzero common orthogonal vector gives a left quadratic form at least $`(3/8)\|w\|_2^2`$ and a right quadratic form at most $`(\sqrt2/4)\|w\|_2^2`$. The strict scalar gap follows from the kernel-checked LeanCert certificate $`2<9/4`$. The [proof at revision 43b3dc6](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/43b3dc65116633a68c32ec582fd093f3adc95597/matrix-inequalities-and-norms/MI-06/lean) retains the full original complex-matrix and all-unitary target.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The six checked declarations in [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/43b3dc65116633a68c32ec582fd093f3adc95597/matrix-inequalities-and-norms/MI-06/lean/Solution.lean) are:

- `NLA.MI06.modulus_eq_sqrt`: the genuine positive square-root modulus.
- `NLA.MI06.witness_moduli`: six exact moduli, their averages and rank-one decompositions.
- `NLA.MI06.two_vector_orthogonal`: a nonzero common orthogonal vector in complex dimension three.
- `NLA.MI06.witness_quadratic_bounds`: homogeneous bounds for every complex unitary pair.
- `NLA.MI06.counterexample`: the fixed pair defeats all unitary choices.
- `NLA.MI06.not_dominationConjecture`: negation of the complete original assertion.

Two independent agents reviewed the [frozen statements and completed proof](lean/reviews/). [Linux run 34711237623](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34711237623) matched all six exports with the sandboxed Comparator and replayed them through Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) retain all 117 source hashes, isolation checks and rejection controls. All 52 [transitive axiom reports](lean/reviews/proof-build.log) contain only `propext`, `Classical.choice` and `Quot.sound`. These are independent agent reviews, not external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md). On a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce from the verified revision with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-06/lean \
  /absolute/path/to/nla-lean-tools
```

The stronger no-finite-constant theorem in the original manuscript is outside these six formal exports. The original informal proof and its historical audit remain below.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

No finite constant permits the proposed two-unitary Loewner-order domination for the arithmetic symmetric modulus, already in dimension three. A fixed rational example also refutes the proposed $`\sqrt2`$ constant. This concerns matrix order, not a separate norm triangle inequality.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-06-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification above covers the complete original factor-$`\sqrt2`$ target. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For $`X\in\mathbb C^{n\times n}`$, define $`|X|=(X^*X)^{1/2}`$ and

```math
S(X)=\frac{|X|+|X^*|}{2}.
```

For every $`n\ge1`$ and every $`X,Y\in\mathbb C^{n\times n}`$, do there exist unitary $`U,V\in\mathbb C^{n\times n}`$ such that

```math
S(X+Y)\preceq\sqrt2\bigl(U S(X)U^*+V S(Y)V^*\bigr)?
```

Here $`P\preceq Q`$ means $`Q-P`$ is positive semidefinite. The conjectured universal factor $`\sqrt2`$ is already known to be necessary.

## Why it matters

Symmetrizing the left and right polar factors removes their directional preference. The question asks for a precise matrix-order bound for sums, which would yield singular-value and norm consequences for these positive representatives.

## References

1. T. Zhang, *Operator symmetric moduli and sharp triangle inequalities*, arXiv:2603.01046v1 (1 March 2026), §1.2, Conjecture 1.6. [Primary text](https://arxiv.org/html/2603.01046).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), introduction, Theorems 1.1 and 1.3. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-10

Both latest arXiv records remain v1. The June paper supplies related estimates but no proof of the displayed two-unitary inequality. Searches included `Zhang Conjecture 1.6 symmetric moduli`, `arithmetic symmetric modulus Thompson conjecture 2026`, and the two titles with `proof`. No resolution was located. The analogous theorem for the quadratic symmetric modulus is proved and must not be confused with this conjecture; a formula labeled Conjecture 3.13 in arXiv:2606.15624 appears to misidentify the modulus, so the draft follows Zhang's original statement.

**Audit update (2026-09-10):** Rechecked Zhang Conjecture 1.6 and Bourin–Lee Theorem 1.3, with searches for later symmetric-modulus resolutions. Submajorization is weaker than the required two-unitary positive-semidefinite domination. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
