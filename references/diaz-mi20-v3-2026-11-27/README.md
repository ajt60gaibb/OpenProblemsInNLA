# MI-20 Version 3 — Universal Quadratic Upper Bound, Self-Similar Tree Extremizers, Zero-Float Enclosures, and Lean 4 Formalization

- **Author:** Marcio Díaz (Space Research AI, https://spaceresearch.ai, `marcio.diaz@gmail.com`)
- **Date:** 27 November 2026
- **Problem:** [MI-20](../../matrix-inequalities-and-norms/MI-20/README.md) — Sharp subquadratic Lee constants for sums of matrices
- **Version 3 Zenodo DOI:** [`10.5281/zenodo.24608035`](https://doi.org/10.5281/zenodo.24608035) (Concept DOI [`10.5281/zenodo.24591860`](https://doi.org/10.5281/zenodo.24591860))
- **Source Repository (immutable commit):** [`spaceresearchai/mi20-subquadratic-lee@0d223a2`](https://github.com/spaceresearchai/mi20-subquadratic-lee/tree/0d223a24d71c9cb9fbcabd6ddb7103b33c6777d6)
- **Prior Version 1 Archive:** [`references/diaz-mi20-2026-11-27/`](../diaz-mi20-2026-11-27/README.md) (PR #397, DOI `10.5281/zenodo.24591861`)

## Scope and Results

This Version 3 submission expands Version 1 (Theorems 1–4 and Proposition 5) in [`mi20_subquadratic_lee_whitepaper.pdf`](mi20_subquadratic_lee_whitepaper.pdf) while keeping Problem **MI-20** as **Open** (since the exact closed-form value and global optimality of the infinite-tree fixed point across all $1 < p < 2$ and $m \ge 2$ remain open):

1. **Same-Dimension Lemma 2$'$ and Theorem 5 (Lean 4 verified):** Fixed-dimension unitary-free PSD-splitting and POVM infimum reformulations of $(C_{p,m}(n))^{-p}$ without dimension inflation, plus the $m = 2$ orthogonal-projection corollary.
2. **Theorem 6 (Lean 4 verified from $p_0 = 1$, including $p_1 = 2$):** Fixed-dimension formalization via Hadamard's three-lines theorem of Sidney Holden's complex-interpolation log-convexity bound in $1/p$.
3. **Theorem 7, Proposition 8, and Theorem 8:** Concentration-compactness dichotomy ruling out mass splitting in $(\mathcal{S}_p(\ell^2))^m$; exact two-term quadratic asymptotic law $C_{p,m}(2) = 1 + c_2(p-1)^2 - c_2(p-1)^3 + O((p-1)^4)$ as $p \to 1^+$; and unconditional infinite-dimensional full-rank sum $\ker(S) \cap \overline{\mathrm{ran}(H)} = \{0\}$ with onto-isometric polar factors $U_k U_k^* = I_{\overline{\mathrm{ran}(H)}}$ and $0 \in \sigma(H^{-1/2}|A_k|H^{-1/2})$.
4. **Theorem 9 (Lean 4 verified):** Universal Commutator Theorem $[D, G_j^\kappa - D G_j^{\kappa-1} D] = 0$ on Holden's positive power system $(D + H_j)^{2\kappa-1} = \Lambda D^{1/2} G_j^{\kappa-1} D^{1/2}$ ($\kappa = \frac{p}{2(p-1)}$), Power-Variance Lemma, and Top-Eigenspace Spectral Dichotomy on $E_{\max} = \ker(D - d_{\max} I)$.
5. **Theorem 10 (Lean 4 verified):** Universal pure-algebraic upper bound $\sigma_+(\Lambda) = h_+(\Lambda)^{\kappa-1}(h_+(\Lambda) - 1) \le (m - 1)\frac{(\kappa-1)^{\kappa-1}}{\kappa^\kappa}$ for all $1 < p < 2$ and $m \ge 2$, yielding:
   - closed-form radical caps $\Lambda \le \frac{13+16\sqrt{2}}{4} < \frac{891}{100}$ ($p = 4/3, m = 2$) and $\Lambda \le \frac{49\sqrt{3}}{18} < \frac{472}{100}$ ($p = 3/2, m = 2$),
   - the first dimension-free non-asymptotic quadratic bound $\ln C_{p,m}(\infty) \le \frac{m^2 - 1}{2p^2}(p - 1)^2$, and
   - the sharp asymptotic Lambert-$W$ constant $K_m = \frac{c_m^2 + 2c_m}{2}$ ($c_m = W_0((m-1)/e)$, $K_2 \approx 0.317236$), tightening Holden's interpolated bound across $1 < p \le 1.22$ by up to $230\times$ without computer assistance.
6. **Theorem 11 (zero-float certified):** Explicit self-similar infinite-tree extremizers on $\ell^2(\mathcal{T}_s)$ ($\sum_{i=2}^s d_i < 1$). Depth-2 truncations of $s = 5$ ($42\times 42$) yield zero-float certified lower bounds in [`lower_record_certificates.json`](lower_record_certificates.json):
   - $C_{4/3,2}(\infty) > 1.0183715755$ (exceeding Holden's $1.018371575$; certified $\ge 1.01837157550926$),
   - $C_{3/2,2}(\infty) > 1.03643716806$ (certified $\ge 1.03643716806442$).
7. **Theorem 12 (zero-float certified):** Unconditional Two-State Pinch 2-letter reduction using the operator bounds $H_j \preceq h_+(\Lambda) D$ ($p = 4/3$) and $M_j \preceq \sqrt{h_+(\Lambda)}\,I$ ($p = 3/2$), with 4-corner shared-multiplier SOS rectangles certified by exact rational $LDL^\top$ and identically zero polynomial residuals ([`upper_bound_certificates.json`](upper_bound_certificates.json)):
   - $C_{4/3,2}(\infty) \le (17209/16000)^{1/4} \le 1.018377775572$ ($27.2\times$ tighter gap than Holden's $(861/800)^{1/4} \approx 1.0185404735$, using 5 rectangles and 8–14 moment variables),
   - $C_{3/2,2}(\infty) \le (5567/5000)^{1/3} \le 1.036454891841$ ($459\times$ tighter gap than Holden's interpolated $1.0445834539$, using 8 rectangles).
   - Combined with Theorems 6 and 10, this strictly improves the best known certified upper bound on $C_{p,2}(\infty)$ for every $p \in (1, 2)$.

## Machine-Checked Lean 4.33.1 + Mathlib Formalization

The bundled [`lean/`](lean/) project (`leanprover/lean4:v4.33.1`, pinned Mathlib in `lean/lake-manifest.json`, 10 proof modules, 12,206 lines) builds cleanly with zero `sorry` and zero compiler warnings. All 28 exported top-level theorems in [`lean/MI20/AxiomAudit.lean`](lean/MI20/AxiomAudit.lean) depend exclusively on Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`:

- `MI20.prop0_subgradient_bound`, `MI20.lemma1_universal_rank_deficiency`, `MI20.lemma2_full_rank_sum`, `MI20.lemma2_same_dim_full_rank_sum`, `MI20.lemma3_polar_optimality`, `MI20.lemma3_kernel_map`, `MI20.psdPow_mono_of_posSemidef`, `MI20.lemma4a_rank_one_smoothness`, `MI20.lemma4b_kernel_lifting`, `MI20.prop5_superquadratic_obstruction`
- `MI20.theorem1_strict_hierarchy`, `MI20.theorem1_no_finite_extremizer`, `MI20.schattenNorm_sq_le_trace_mul_rpow`, `MI20.theorem3_universal_2x2_collapse`, `MI20.theorem3_exact_p32`, `MI20.theorem4_witness_p32`
- `MI20.theorem5_psd_reformulation`, `MI20.theorem5_povm_reformulation`, `MI20.theorem6_interp_from_one`, `MI20.theorem6_p2_upper_bound`
- `MI20.universal_commutator_identity`, `MI20.universal_commutator_theorem`, `MI20.power_variance_lemma`, `MI20.top_eigenspace_spectral_dichotomy`, `MI20.universal_algebraic_upper_bound`, `MI20.universal_bound_p43_m2`, `MI20.universal_bound_p32_m2`, `MI20.universal_quadratic_log_bound`

A standalone zero-dependency Lean 4 companion file [`MI20_FormalProof.lean`](MI20_FormalProof.lean) (1,004 lines) is also included.

## Reproduction

```bash
# 1. Zero-floating-point master verifier (Python 3 stdlib only; Suites 1-4: Thm 4, Thm 11, Thm 12, tamper tests):
python3 -B -S references/diaz-mi20-v3-2026-11-27/verify_all_exact_certificates.py

# 2. Full 10-module Lean 4.33.1 + Mathlib build & 28-theorem axiom audit:
cd references/diaz-mi20-v3-2026-11-27/lean && lake build && lake env lean MI20/AxiomAudit.lean

# 3. Standalone zero-dependency Lean 4 check:
lean references/diaz-mi20-v3-2026-11-27/MI20_FormalProof.lean
```

## Audit Notes

- **Theorem 2 Step 1 fix:** The singular-vector direction slip in Theorem 2 Step 1 flagged during the PR #397 audit of Version 1 is fixed in [`mi20_subquadratic_lee_whitepaper.pdf`](mi20_subquadratic_lee_whitepaper.pdf).
- **Lean scope vs. paper-only and Python-certified scope:** The Lean 4.33.1 + Mathlib project formally verifies the complex finite-dimensional backbone (Theorems 1, 3 for $1<p<2$ and $p=3/2$, 4 at $p=3/2$, 5, 6 from $p_0=1$, Proposition 0, Lemmas 1–4, Lemma 2$'$, Proposition 5) and the universal algebraic power-system bounds (Theorems 9 and 10). Infinite-dimensional Hilbert-space results (Theorems 2, 7, 8), Corollary 1, Theorem 3(2), Theorem 5's $m=2$ corollary, Proposition 8, and the analytic operator reductions of Theorems 11–12 are proved on paper, while all numerical inequalities in Theorems 4, 11, and 12 are checked without floating-point arithmetic by `verify_all_exact_certificates.py`.
- **Review status:** Author submission with local Lean 4.33.1 + Mathlib build/axiom checks and zero-float Python verification; no external human peer review or catalog-side independent Lean Comparator run has been performed yet.
