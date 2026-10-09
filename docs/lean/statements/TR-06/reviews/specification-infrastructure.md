# TR-06 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the TR-06 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is a statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-06/README.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
| `docs/lean/statements/TR-06/ORIGINAL.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
| `docs/lean/statements/TR-06/NUMERICAL_TARGETS.md` | `ccc0528ad0404fcd6b5e7d3fcb31e68a65904fd631e052417fcd281480d60a16` |

The canonical README and retained `ORIGINAL.md` are byte identical. The permanent ID and canonical path agree with `problem_ids.json`.

## Exact probability and condition-number comparison

The specification quantifies over every tensor order `d≥3`, each real factor dimension at least two, and every rank `r≥3` satisfying the original **generic complex** identifiability assumption. It distinguishes this from a real-only or one-format assumption, and correctly notes that rank two is background rather than part of the target. It keeps the smooth identifiable locus of **real rank-r tensors** with the Euclidean volume induced by the ambient Frobenius metric.

The probability law is the normalized density `exp(−‖A‖_F²/2)` against that induced volume, with the actual normalizer. It is not the distribution obtained by independently sampling rank-one summands. The addition map has actual rank-one inputs, its inverse is local on an identifiable branch, and the unordered ambiguity is harmless for the product Frobenius norm. Each inverse output is normalized **individually before differentiation**. The angular condition number is the operator norm of `D(p^{×r}∘Ψ)` from the induced tangent norm to the product norm, not the ordinary inverse derivative or a scalar divided version.

The proposition is strict finiteness of the expectation of that exact angular condition number for every admissible format. It requires no explicit or format-uniform constant and changes on measure-zero exceptional sets do not affect it. The specification neither adds a finite mean claim for the ordinary condition number nor replaces the original measure. I found no missing rank, format, derivative, measure, or integrability condition.
