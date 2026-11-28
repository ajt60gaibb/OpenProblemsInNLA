# MI-20 Version 6 — Exact All-$m$ Resolution at $p = 4/3$, Universal Global Asymptotics, Zero-Float Multi-$p$ Enclosures, Scalar-Kernel Obstruction, and 131-Theorem Bare Lean 4.35.0 Formalization

- **Author:** Marcio Diaz (Space AI, https://spaceresearch.ai, `marcio.diaz@gmail.com`)
- **Date:** 28 November 2026
- **Problem:** [MI-20](../../matrix-inequalities-and-norms/MI-20/README.md) — Sharp subquadratic Lee constants for sums of matrices (**Status remains Open** for exact evaluation at $p \neq 4/3$)
- **Version 6 Zenodo DOI:** [`10.5281/zenodo.24625177`](https://doi.org/10.5281/zenodo.24625177) ([Zenodo Record](https://zenodo.org/records/24625177); Concept DOI [`10.5281/zenodo.24625176`](https://doi.org/10.5281/zenodo.24625176))
- **Prior Releases (preserved intact):**
  - Version 5: [`references/diaz-mi20-v5-2026-11-28/`](../diaz-mi20-v5-2026-11-28/README.md) (DOI [`10.5281/zenodo.24621394`](https://doi.org/10.5281/zenodo.24621394), 73-theorem Lean 4.33.1 + Mathlib formalization, BCH $K_2^{\mathrm{BCH}} < 0.3145$, Hirota solitons, Suites 1–6)
  - Version 1: [`references/diaz-mi20-2026-11-27/`](../diaz-mi20-2026-11-27/README.md) (PR #397, DOI [`10.5281/zenodo.24591861`](https://doi.org/10.5281/zenodo.24591861))
- **Foundational Attribution:** Builds on Eun-Young Lee (2010) and **Sidney Holden** (September 12–13, 2026: complex interpolation, cyclic reduction, Theorem 3.1, and prior $p = 4/3, m = 2$ record $1.018371575 < C_{4/3}(2) \le 1.01854047$).

## Scope and New Results (Building on Version 5)

All Version 5 deliverables in `references/diaz-mi20-v5-2026-11-28/` remain completely intact. This companion **Version 6** monograph ([`MI20_Exact_p43_Global_Asymptotics_Diaz_2026.pdf`](MI20_Exact_p43_Global_Asymptotics_Diaz_2026.pdf), 33 pages, 3 figures) establishes:

1. **Exact All-$m$ Resolution at $p = 4/3$ (Theorem 14):** Proves unconditionally for **every** integer $m \ge 2$ and **every** dimension $n \ge 1$ that
   $$C_{4/3}^{\mathbb{R}}(m) = C_{4/3}^{\mathbb{C}}(m) = \left(\frac{\Lambda_*(m)}{8}\right)^{1/4}, \qquad T_0(\Lambda_*(m)) = \frac{m}{m - 1}\,\sigma_+(\Lambda_*(m)),$$
   where $T_0(\Lambda)$ is the continuum RKHS capacity of $M_{0,\Lambda}(x, y)$ on $[0, x_+(\Lambda))^2$. Combines a purely analytic Gap 1A lower bound (conic Fekete maximizer, 4-line Trace Killer, nonnegative equilibrium measure $\nu_0 \ge 0$, $g_0 \equiv 1$, algebraic all-$m$/all-$r$ branching $\rho_r < 1$), a 4-line uninverted operator bridge handling arbitrary top/non-top/degenerate eigenvalues, and zero-float `mpmath.iv` Part 1 & Part 2 certification (`rigorous_iv_p43_all_m_part1.py` & `part2.py`, 630,000+ pure-interval boxes, AST zero-float audited).
2. **Complete Purely Analytic Global Asymptotics Across All $1 < p < 2, m \ge 2$ (Zero Computers, Theorems 8, 15–18):**
   - Exact real–complex equality $C_p^{\mathbb{R}}(m) = C_p^{\mathbb{C}}(m)$ for all $1 \le p \le \infty, m \ge 2$ via 2-line realification $*$-homomorphism.
   - **Universal Exact Two-Term Large-$m$ Law** for every $1 < p < 2$: $C_p(m) = 2^{-1/p} m^{\frac{1}{2}(1-1/p)}\big(1 + \frac{1}{2} m^{-(1-1/p)} + O_p(m^{-\min(2(1-1/p),\,\frac{p-1}{2-p})})\big)$, beating Riesz–Thorin complex interpolation by the exact factor $2^{2/p-1} > 1$, plus the **exact 5-term expansion** and **exact leading continuum excess** $C_{4/3}(m) - C_{1\times 1}(4/3, m) = \frac{1}{8\cdot 2^{3/4}} m^{-7/8} + O(m^{-9/8})$ at $p = 4/3$.
   - **Exact $p \to 1^+$ Lambert-$W$ curvature law:** $\Theta((\log m)^2)(p - 1)^2$ for every $m \ge 2$ (exponentially sharper in $m$ than $O(m^2)$).
   - **Super-exponential $p \to 2^-$ collapse & infinite-order contact for ALL $m \ge 2$:** $0 \le C_p(m) - C_{1\times 1}(p, m) = O_m((2-p)(1+\sqrt{m})^{-\frac{2(p-1)}{2-p}})$ plus the exact left slope at $p = 2^-$.
   - **Unconditional all-$p$ operator laws:** $[E_j, D] = 0$, self-contained 3-line proof of $0 < H_j \le x_+(\Lambda) D$ for all $\kappa > 1$, 6-line Universal Positivity Rigidity, and purely analytic all-$m$ SOS bounds at $p \in \{5/3, 3/2, 4/3, 5/4, 6/5\}$.
3. **Zero-Float `mpmath.iv` Multi-$p$ World Records & Continuous Global Enclosures (Section 7, all $n \ge 1$):**
   - Tightens every Version 5 multi-summand bound by $2.47\times$ to $646\times$ (outward-rounded):
     - $p = 4/3$: `1.018371575517 < C_{4/3}(2) <= 1.018371857816` ($11.5\times$ tighter than v5), `1.031863848072 < C_{4/3}(3) <= 1.031864665403` ($250\times$), `1.042812616134 < C_{4/3}(4) <= 1.042814769284` ($123\times$), plus exact equality for all $m \ge 2$.
     - $p = 3/2$: `1.036437168065 < C_{3/2}(2) <= 1.036437592480` ($2.47\times$, gap `4.24e-7`), `1.063114500990 < C_{3/2}(3) <= 1.063115168558` ($338\times$), `1.084719139101 < C_{3/2}(4) <= 1.084719713538` ($646\times$).
     - $p = 5/4$: `1.011065979791 < C_{5/4}(2) <= 1.011092421533` ($55\times$ tighter than v5) + first $m = 3, 4$ bounds.
     - First zero-float two-sided enclosures at $p = 6/5$ ($m=2,3,4$, gap `1.82e-5` at $m=2$) and $p = 5/3$ ($m=2,3,4$, gap `5.89e-6` at $m=2$).
   - **7-anchor global complex-interpolation envelope** (`rigorous_iv_global_interpolation.py`, 604 crack-free boxes, whole-file zero-float AST audit): strictly dominates Holden's prior curve at every real $p \in (1, 2)$ ($\ge 3.54\times$ tighter uniform global error for $m=2$, $\ge 11.6\times$ for $m=4$).
   - **36 rational & irrational universal-dual bounds + continuous $[1.50, 1.99]$ cover** (`rigorous_iv_universal_dual_all_p.py`): certified strict noncommuting $8\times 8$ matrix gains even at irrational $p = \sqrt{2}, \phi$, gaps down to `2.07e-9` at $p = 1.95$, and 267 2D boxes beating complex interpolation for every real $p \in [1.50, 1.99]$.
4. **Scalar-Kernel Uniqueness Obstruction & Unified Bare Lean 4.35.0 Formalization (Sections 8–9):**
   - Proves via the exact Diagonal Row-Variance Identity why $p = 4/3$ ($\kappa = 2$) is the unique exponent admitting a solution-independent scalar Hadamard kernel (disproving it at $p = 3/2, 6/5$) and diagnoses the convex-relaxation and Stage-1 $U = L_{\mathrm{cs}}$ obstructions for $p \neq 4/3$.
   - [`MI20_FormalProof.lean`](MI20_FormalProof.lean): **2,910 lines**, **131 `theorem` declarations**, **57 `#print axioms`-audited top-level theorems**, bare Lean 4.35.0 (zero Mathlib, zero `sorry`, zero warnings, standard axioms only).

## Reproduction

```bash
# 1. Bare Lean 4.35.0 formalization check (0 errors, 0 warnings, 0 sorry, ~5 s):
lean references/diaz-mi20-v6-exact-p43-2026-11-28/MI20_FormalProof.lean

# 2. All-m exact p=4/3 zero-float mpmath.iv certification (Part 1 ~48 s; Part 2 ~9.5 min on 10 cores):
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_p43_all_m_part1.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_p43_all_m_part2.py

# 3. Tight p=4/3 (m=2,3,4), multi-p (6/5, 5/4, 3/2, 5/3), global interpolation, and universal dual:
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_proof_p43.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_lower_bounds_p43.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_multi_p_bounds.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_global_interpolation.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/rigorous_iv_universal_dual_all_p.py

# 4. Symbolic (SymPy) and high-precision analytic theorem verifiers:
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/verify_p43_operator_bridge.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/explore_general_p_theory.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/verify_general_p_operator_bridge.py
python3 references/diaz-mi20-v6-exact-p43-2026-11-28/verify_general_p_deep_closure.py
```

## Audit Notes

- **Epistemic transparency:** Every theorem in `MI20_Exact_p43_Global_Asymptotics_Diaz_2026.pdf` is explicitly labeled as *Purely Analytic*, *Zero-Float `mpmath.iv` Certified*, *Lean 4.35.0 Machine-Checked*, *Verified Numerical*, or *Open Conjecture*. All upper bounds in Sections 4–7 rely on Sidney Holden's Theorem 3.1 (September 2026); all finite-dimensional hierarchy, realification, and lower-bound constructions are independent of Holden's theorem.
- **Review status:** Author submission with local zero-float `mpmath.iv` AST audits, symbolic/high-precision checks, independent multi-agent adversarial review, and bare Lean 4.35.0 compilation; no external human peer review or catalog-side independent verification has been performed yet. Problem **MI-20** remains strictly **Open** for exact evaluation at $p \in (1, 2) \setminus \{4/3\}$.
