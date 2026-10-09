# TR-17 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the TR-17 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is a statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-17/README.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/ORIGINAL.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/NUMERICAL_TARGETS.md` | `08d4027ca2d185945da636498173fb90fcec4d5d565a22a839090ea6c94eb120` |

The canonical README and retained `ORIGINAL.md` are byte identical. The permanent ID and canonical path agree with `problem_ids.json`.

## Exact algebraic and metric comparison

The specification quantifies over every factor count `k≥1`, every factor dimension `n_j≥2`, and positive symmetric degree `d_j≥1` with total tensor order at least three. It retains the real partially symmetric tensor space and its complexification, and defines the entire affine Segre–Veronese rank-one cone as arbitrary complex scalar multiples of factorwise pure symmetric powers, including zero. The critical count excludes singular and zero cone points by using the smooth nonzero locus; it does not choose one convenient format or add a genericity assumption on the metric.

The metric ranges over **all** positive definite symmetric real bilinear forms on that real tensor space, extended to complex tensors **bilinearly**. The objective is the squared distance `Q(A−Z,A−Z)`, with complex critical points for **Zariski-generic** complex data `A`. The ED degree counts critical points with **algebraic multiplicity**, so a finite generic critical scheme/fiber length is an apt concrete implementation. Reduced point count, real-only count, one selected datum, or a metric-generic theorem would weaken the target.

The benchmark metric is the restriction of the full entrywise Frobenius inner product from the unsymmetrized tensor product. Its repeated ordered entries induce combinatorial weights in symmetric coordinates; an unweighted coefficient dot product would be wrong. The final inequality `ED_Q(X)≥ED_QF(X)` is an exact natural-number comparison for every admissible format and every positive definite `Q`, with no probability, approximation factor, or asymptotic qualifier. I found no missing quantifier or changed algebraic, multiplicity, or metric convention.
