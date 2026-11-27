# MI-20 Version 4 — Sharp Universal & Super-Exponential Collapse Bounds, Exact BCH Limit, Zero-Float Enclosures, and 40-Theorem Lean 4 Formalization

- **Author:** Marcio Díaz (Space Research AI, https://spaceresearch.ai, `marcio.diaz@gmail.com`)
- **Date:** 28 November 2026
- **Problem:** [MI-20](../../matrix-inequalities-and-norms/MI-20/README.md) — Sharp subquadratic Lee constants for sums of matrices
- **Version 4 Zenodo DOI:** [`10.5281/zenodo.24612832`](https://doi.org/10.5281/zenodo.24612832) (Concept DOI [`10.5281/zenodo.24591860`](https://doi.org/10.5281/zenodo.24591860))
- **Source Repository (immutable commit):** [`spaceresearchai/mi20-subquadratic-lee@e189578`](https://github.com/spaceresearchai/mi20-subquadratic-lee/tree/e1895782f6fe300fa2560914e4f1c222a73ac7b3) (Release [`v4.0`](https://github.com/spaceresearchai/mi20-subquadratic-lee/releases/tag/v4.0))
- **Prior Version 1 Archive:** [`references/diaz-mi20-2026-11-27/`](../diaz-mi20-2026-11-27/README.md) (PR #397, DOI `10.5281/zenodo.24591861`)

## Scope and Results

This Version 4 submission expands Version 1 (Theorems 1–4 and Proposition 5) in [`mi20_subquadratic_lee_whitepaper.pdf`](mi20_subquadratic_lee_whitepaper.pdf) while keeping Problem **MI-20** as **Open** (since the exact closed-form value and global optimality of the infinite-tree fixed point across all $1 < p < 2$ and $m \ge 2$, as well as ruling out total spectral vanishing in Theorem 7, remain open):

1. **Same-Dimension Lemma 2$'$ and Theorem 5 (Lean 4 verified):** Fixed-dimension unitary-free PSD-splitting and POVM infimum reformulations of $(C_{p,m}(n))^{-p}$ without dimension inflation, plus the $m = 2$ orthogonal-projection corollary.
2. **Theorem 6 (Lean 4 verified from $p_0 = 1$, including $p_1 = 2$):** Fixed-dimension formalization via Hadamard's three-lines theorem of Sidney Holden's complex-interpolation log-convexity bound in $1/p$.
3. **Theorem 7, Proposition 8, and Theorem 8:** Concentration-compactness dichotomy ruling out mass splitting in $(\mathcal{S}_p(\ell^2))^m$; exact two-term quadratic asymptotic law $C_{p,m}(2) = 1 + c_2(p-1)^2 - c_2(p-1)^3 + O((p-1)^4)$ as $p \to 1^+$; and unconditional infinite-dimensional full-rank sum $\ker(S) \cap \overline{\mathrm{ran}(H)} = \{0\}$ with onto-isometric polar factors $U_k U_k^* = I_{\overline{\mathrm{ran}(H)}}$ and $0 \in \sigma(H^{-1/2}|A_k|H^{-1/2})$.
4. **Theorem 9 (Lean 4 verified):** Universal Commutator Theorem $[D, G_j^\kappa - D G_j^{\kappa-1} D] = 0$ on Holden's positive power system $(D + H_j)^{2\kappa-1} = \Lambda D^{1/2} G_j^{\kappa-1} D^{1/2}$ ($\kappa = \frac{p}{2(p-1)}$), Power-Variance Lemma, and Top-Eigenspace Spectral Dichotomy on $E_{\max} = \ker(D - d_{\max} I)$.
5. **Theorem 10 (Lean 4 verified):** Universal pure-algebraic upper bound $\sigma_+(\Lambda) \le (m - 1)\frac{(\kappa-1)^{\kappa-1}}{\kappa^\kappa}$ for all $1 < p < 2$ and $m \ge 2$, yielding closed-form radical caps $\Lambda < 891/100$ ($p = 4/3, m = 2$) and $\Lambda < 472/100$ ($p = 3/2, m = 2$), the first dimension-free non-asymptotic quadratic bound $\ln C_{p,m}(\infty) \le \frac{m^2 - 1}{2p^2}(p - 1)^2$, and the Lambert-$W$ asymptotic constant $K_m = \frac{c_m^2 + 2c_m}{2}$ ($K_2 \approx 0.317236$).
6. **Theorem 10A (Lean 4 verified):** Sharp one-line universal bound $(1 + h_+(\Lambda))^{2\kappa-1}(h_+(\Lambda) - 1) \le (m - 1)\frac{(2\kappa - 1)^{2\kappa - 1}}{\kappa^{2\kappa}}$ for all $1 < p < 2$ and $m \ge 2$ — strictly dominating Theorem 10 everywhere, exact in the Frobenius limit $p \to 2^-$ ($C_{2,m} = \sqrt{(1+\sqrt{m})/2}$ for all $m \ge 2$), and directly beating Holden at $p = 3/2$ ($\Lambda < 451/100 \implies C_{3/2,2} \le 1.039968$), $p = 5/4$, $p = 5/3$, and $p = 7/4$ with zero SDP.
7. **Theorem 10B (Lean 4 verified):** Coupled two-function universal bound with closed-form weighted AM–GM regimes across $1 < p < 2$ and the explicit $B = \frac{1}{2 - p}$ **$C^\infty$-flat super-exponential collapse law** $0 < C_{p,2}(\infty) - C_{p,2}(2) = O\bigl((1 + \sqrt{2})^{-\frac{2(p-1)}{2-p}}\bigr)$ as $p \to 2^-$ — pinning $C_{1.95,2}(\infty)$ to 14 digits (gap $1.98\times 10^{-14}$), $C_{1.90,2}(\infty)$ to 10 digits, $C_{1.85,2}(\infty)$ to 7 digits, beating Holden by $471\times$ at $p = 7/4$ ($C_{7/4,2} \le 1.0681498$) and $68.7\times$ at $p = 5/3$ ($C_{5/3,2} \le 1.0574723$) with zero SDP, and proving complete-square caps $\Lambda < 447/100$ ($C_{3/2,2} \le 1.037312$, $9.1\times$ tighter than Holden) and $\Lambda < 866/100$ ($C_{4/3,2} \le 1.019895$).
8. **Theorem 10C (Lean 4 verified):** Two-line pure-algebraic Bessel identity and bound at $p = 4/3$ for all $m \ge 2$ ($C_{4/3,2}(\infty) \le 1.018930$, $C_{4/3,3}(\infty) \le 1.032735$, $C_{4/3,4}(\infty) \le 1.043885$, $C_{4/3,10}(\infty) \le 1.087759$, zero SDP).
9. **Theorem 11 (zero-float certified):** Explicit self-similar infinite-tree extremizers on $\ell^2(\mathcal{T}_s)$ with sharp $\mathcal{S}_p$-summability $(m - 1)\sum_{i=2}^s d_i^{2\kappa} < 1$. Depth-2 truncations of $s = 5$ ($42\times 42$) yield zero-float certified lower bounds in [`lower_record_certificates.json`](lower_record_certificates.json):
   - $C_{4/3,2}(\infty) > 1.0183715755$ (exceeding Holden's $1.018371575$; certified $\ge 1.01837157550926$),
   - $C_{3/2,2}(\infty) > 1.03643716806$ (certified $\ge 1.03643716806442$).
10. **Theorem 12 (zero-float certified):** Unconditional Two-State Pinch 2-letter reduction together with strict convexity $\sigma_+'(\Lambda) = \bigl(\frac{h_+(\Lambda)}{1 + h_+(\Lambda)}\bigr)^{2\kappa - 2}$, 4-corner shared-multiplier SOS rectangles and convex trapezoids, and ray-free State-2 bases certified by exact rational $LDL^\top$ with identically zero polynomial residuals ([`upper_bound_certificates.json`](upper_bound_certificates.json)):
    - $C_{4/3,2}(\infty) \le (21511/20000)^{1/4} \le 1.018374816707$ ($52.1\times$ tighter gap than Holden's $(861/800)^{1/4} \approx 1.0185404735$, using 7 pieces with `proj = 0` on every piece),
    - $C_{3/2,2}(\infty) \le (890677/800000)^{1/3} \le 1.036438213095$ ($7{,}795\times$ tighter gap than Holden's interpolated $1.0445834539$, using 11 pieces; total enclosure width $1.05\times 10^{-6}$).
    - Combined with Theorems 6, 10A, and 10B, this strictly improves the best known certified upper bound on $C_{p,2}(\infty)$ across every $p \in (1, 2)$.
11. **Theorem 13:** Exact $p \to 1^+$ Baker–Campbell–Hausdorff Lie–Trotter operator limit $\operatorname{Dexp}_{-M_j}[U_j^2] = 4a_L e^{-M_j} - 2\Phi_{\lim,j}$, hyperbolic eigenbasis identities $(W^2)_{ii} = 1 + 4a_L$ and $(W^2)_{ij} = 2\bigl(\frac{\Delta_{ij}}{\tanh\Delta_{ij}} - 1\bigr)W_{ij}$, geometric tree limit $K_2^{\mathrm{tree}}(\infty) = 0.2259284\dots$, and sharp $\mathcal{S}_p$-summability criterion $(m - 1)\sum_{i=2}^s d_i^{2\kappa} < 1$.

## Machine-Checked Lean 4.33.1 + Mathlib Formalization

The bundled [`lean/`](lean/) project (`leanprover/lean4:v4.33.1`, pinned Mathlib in `lean/lake-manifest.json`, 11 proof modules, 13,770 lines) builds cleanly with zero `sorry` and zero compiler warnings. All 40 exported top-level theorems in [`lean/MI20/AxiomAudit.lean`](lean/MI20/AxiomAudit.lean) depend exclusively on Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`:

- `MI20.prop0_subgradient_bound`, `MI20.lemma1_universal_rank_deficiency`, `MI20.lemma2_full_rank_sum`, `MI20.lemma2_same_dim_full_rank_sum`, `MI20.lemma3_polar_optimality`, `MI20.lemma3_kernel_map`, `MI20.psdPow_mono_of_posSemidef`, `MI20.lemma4a_rank_one_smoothness`, `MI20.lemma4b_kernel_lifting`, `MI20.prop5_superquadratic_obstruction`
- `MI20.theorem1_strict_hierarchy`, `MI20.theorem1_no_finite_extremizer`, `MI20.schattenNorm_sq_le_trace_mul_rpow`, `MI20.theorem3_universal_2x2_collapse`, `MI20.theorem3_exact_p32`, `MI20.theorem4_witness_p32`
- `MI20.theorem5_psd_reformulation`, `MI20.theorem5_povm_reformulation`, `MI20.theorem6_interp_from_one`, `MI20.theorem6_p2_upper_bound`
- `MI20.universal_commutator_identity`, `MI20.universal_commutator_theorem`, `MI20.power_variance_lemma`, `MI20.top_eigenspace_spectral_dichotomy`, `MI20.universal_algebraic_upper_bound`, `MI20.universal_bound_p43_m2`, `MI20.universal_bound_p32_m2`, `MI20.universal_quadratic_log_bound`
- `MI20.exists_negative_flux_eigenvector`, `MI20.universal_sharp_one_line_bound`, `MI20.sharp_one_line_cap_p43_m2`, `MI20.sharp_one_line_cap_p32_m2`, `MI20.sharp_one_line_p2_limit_frobenius`, `MI20.universal_two_function_bound`, `MI20.two_function_regime1_bound`, `MI20.two_function_regime2_bound`, `MI20.superexponential_p2_collapse_bound`, `MI20.two_function_cap_p32_m2`, `MI20.two_function_cap_p43_m2`, `MI20.bessel_two_line_identity_p43`

A standalone zero-dependency Lean 4 companion file [`MI20_FormalProof.lean`](MI20_FormalProof.lean) (1,004 lines) is also included.

## Reproduction

```bash
# 1. Zero-floating-point master verifier (Python 3 stdlib only, 0.32 s; Suites 1-4: Thm 4, Thm 11, Thm 12, 4 tamper tests):
python3 -B -S references/diaz-mi20-v4-2026-11-28/verify_all_exact_certificates.py

# 2. Full 11-module Lean 4.33.1 + Mathlib build & 40-theorem axiom audit:
cd references/diaz-mi20-v4-2026-11-28/lean && lake build && lake env lean MI20/AxiomAudit.lean

# 3. Standalone zero-dependency Lean 4 check:
lean references/diaz-mi20-v4-2026-11-28/MI20_FormalProof.lean
```

## Audit Notes

- **Theorem 2 Step 1 fix:** The singular-vector direction slip in Theorem 2 Step 1 flagged during the PR #397 audit of Version 1 is fixed in [`mi20_subquadratic_lee_whitepaper.pdf`](mi20_subquadratic_lee_whitepaper.pdf).
- **Lean scope vs. paper-only and Python-certified scope:** The Lean 4.33.1 + Mathlib project formally verifies the complex finite-dimensional backbone (Theorems 1, 3 for $1<p<2$ and $p=3/2$, 4 at $p=3/2$, 5, 6 from $p_0=1$, Proposition 0, Lemmas 1–4, Lemma 2$'$, Proposition 5) and the universal algebraic power-system bounds (Theorems 9, 10, 10A, 10B, and 10C). Infinite-dimensional Hilbert-space results (Theorems 2, 7, 8, and 13), Corollary 1, Theorem 3(2), Theorem 5's $m=2$ corollary, Proposition 8, and the analytic operator reductions of Theorems 11–12 are proved on paper, while all numerical inequalities in Theorems 4, 11, and 12 are checked without floating-point arithmetic by `verify_all_exact_certificates.py`.
- **Review status:** Author submission with local Lean 4.33.1 + Mathlib build/axiom checks and zero-float Python verification; no external human peer review or catalog-side independent Lean Comparator run has been performed yet.
