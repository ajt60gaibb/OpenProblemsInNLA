# TR-01 — Optimal dimension for a rerandomized Hadamard embedding

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because two structured randomizations must remove the embedding logarithm uniformly over subspaces; community impact is fast sketching for least squares and low-rank methods.  
**Status:** Lean verified  
**Last checked:** 2026-09-12  

> **LEAN VERIFIED — complete affirmative resolution.** TR-01 is resolved by the v7 manuscript theorem with full two-randomization rerandomized SRHT statement at prescribed width. The result is not a weaker-width selection. This retained entry is excluded from the open count.

## Problem statement

Let $n$ be a power of two, $1\le r\le n$, and $0<\varepsilon<1/2$. Let $F$ be the normalized Walsh–Hadamard matrix, let $D_1,D_2$ have independent Rademacher diagonal entries, and let $S\in\mathbb R^{n\times k}$ select a uniformly random $k$-element subset of coordinates, independently. Set

$$
\Omega=\sqrt{n/k}\,D_1FD_2FS.
$$

Does a universal $C>0$ exist such that, for every fixed $r$-dimensional subspace $V\subseteq\mathbb R^n$, choosing $k=\min\{n,\lceil Cr/\varepsilon^2\rceil\}$ gives

$$
\Pr\left\{(1-\varepsilon)\|x\|_2^2\le
\|\Omega^Tx\|_2^2\le(1+\varepsilon)\|x\|_2^2
\text{ for every }x\in V\right\}\ge0.99?
$$

This fixes normalization, sampling without replacement, and a constant success probability in the workshop question. Results for a single randomization, three randomizations, or independently sampled sparse sketches do not establish this statement.

## References

Amsel et al., [*Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*](https://arxiv.org/html/2602.05394v3), §5.3, Definition 5.3 and Problem 5.6. For the single-round baseline, Joel A. Tropp, [*Improved Analysis of the Subsampled Randomized Hadamard Transform*](https://arxiv.org/abs/1011.1595), *Advances in Adaptive Data Analysis* 3 (2011), 115–126, Theorem 3.1.

## Resolution and status check — 2026-09-12

The affine preprint *Subspace embeddings with the rerandomized SRHT* (Theorem 1, manuscript page 2, [arXiv-style full text](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.pdf)) proves that for each power-of-two $n$, every $1\le r\le n$, and every fixed $r$-dimensional subspace $V$, choosing

$$
k=\min\left\{n,\left\lceil Cr/\varepsilon^2\right\rceil\right\}
$$

gives

$$
\Pr\left\{\|V^T\Omega^T\Omega V-I_r\|_2>\varepsilon\right\}\le0.01,
$$

for two independent Rademacher sign diagonals, two normalized Walsh transforms, and a uniform $k$-subset coordinate sample without replacement. The theorem proves the *prescribed width itself* with full width cap and does not rely on a smaller alternative $k$. The same universal constant works for every power-of-two $n$, and there are no remaining parameter cases.

The proven range is $0<\varepsilon<1$, which strictly contains TR-01’s displayed range $0<\varepsilon<1/2$. This is therefore a complete affirmative resolution of the original target.

The current statement is the TR-01 target at prescribed width; the original 2026 Simons problem version (Problem 5.6) is the same probabilistic target on fixed $V$, and the manuscript explicitly records the comparison of the workshop and current versions.

## Lean proof and verification evidence

The public Lean repository is [OpenProblemsInNLA_TR-01@ed211811](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/tree/ed21181197ac839eac95f549404f94e7e3aa6e10), and the v7 Lean entry point is `lean/Problem56/PaperV7/Certification.lean`.

The canonical result declarations are

- `Problem56.PaperV7.certified_main`
- `Problem56.PaperV7.certified_explicit_main`
- `Problem56.PaperV7.main_prescribed_width_ose`

The manuscript and Lean correspondence are reviewed in

- [manuscript.pdf](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.pdf)
- [manuscript.tex](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.tex)
- [`final_candidate_correspondence.md`](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/final_candidate_correspondence.md)
- [`final_candidate_correspondence.json`](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/final_candidate_correspondence.json)

Lean toolchain and dependency pins are

- [lean-toolchain](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/lean-toolchain) (`lean 4.33.0`)
- [lake-manifest.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/lake-manifest.json) (mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`)

Reproducible checks are listed in the immutable validation record:

- [delivery_check.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/delivery_check.json) (PASS)
- [cold_rebuild.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/cold_rebuild.json) (rebuild log and source hashes)
- [fresh_kernel_replay.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/fresh_kernel_replay.json)
- [semantic_regressions.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/semantic_regressions.json)
- [final_binding_review.json](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/audit/final_binding_review.json)

The axiom audit is in the immutable artifact [`AxiomAudit.lean`](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/lean/Problem56/PaperV7/AxiomAudit.lean), with accepted transitive axioms only

- `propext`
- `Classical.choice`
- `Quot.sound`

No `sorry`, `admit`, or custom mathematical axioms appear in the certified target graph.

The catalog checked the statement correspondence and public verification records and did not rerun Lean locally for this upstream submission.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Solved and claimed solutions](../../RESOLVED.md#tr-01) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
