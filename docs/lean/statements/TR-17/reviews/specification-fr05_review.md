# TR-17 independent pre-implementation specification review

**Verdict: APPROVE.** I did not author this specification. I compared it independently with the canonical README and Colbrook's complete resolution, particularly its Theorem 1 and exact metric convention. This approves the statement target, not a formal proof.

| Reviewed input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-17/README.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/ORIGINAL.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `docs/lean/statements/TR-17/NUMERICAL_TARGETS.md` | `08d4027ca2d185945da636498173fb90fcec4d5d565a22a839090ea6c94eb120` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr17_solution.tex` | `abbaff0249f941e745810173e425b6ce424a0915066088ebdba8f6fc5e9548cb` |

The canonical README and `ORIGINAL.md` are byte identical. The specification quantifies every `k≥1`, each `n_j≥2`, each `d_j≥1`, and total order at least three. It uses the actual partially symmetric real tensor product and the complex affine Segre–Veronese cone including scalar multiples and zero, while counting only the smooth nonzero locus. The order-two matrix case is correctly excluded.

`Q` ranges over **every** positive definite symmetric real bilinear form, then is extended complex-bilinearly without conjugation. The fixed `Q_F` is the restriction of the entrywise Frobenius product on the unsymmetrized tensor product; its repeated-entry weights survive in symmetric coordinates. An unweighted monomial-coefficient metric would change the target and is explicitly disallowed.

Both ED degrees are the algebraic-multiplicity counts of complex critical points of `Z↦Q(A−Z,A−Z)` for Zariski-generic complex `A`, on the smooth nonzero cone. The generic qualification belongs to the data, never to `Q`. The requested result is the exact natural inequality `ED_Q(X)≥ED_QF(X)` for every admissible format and positive definite `Q`, with no probability, asymptotic, local-only, or metric-generic weakening. The specification correctly requires concrete geometric and multiplicity semantics in Lean. No mismatch requiring revision was found.
