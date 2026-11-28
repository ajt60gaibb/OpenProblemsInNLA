# MI-20 Structural Partial Resolution — 27 November 2026

**Author:** Marcio Diaz, Space AI  
**Contact:** `marcio.diaz@gmail.com`  
**Zenodo Preprint:** [10.5281/zenodo.24591861](https://doi.org/10.5281/zenodo.24591861)  
**Target:** [MI-20 — Sharp subquadratic Lee constants for sums of matrices](../../matrix-inequalities-and-norms/MI-20/README.md)

## Scope

This submission provides a **structural partial resolution** of Problem **MI-20**. It does **not** determine the exact closed-form function $C_p(m)$ for $1 < p < 2$ and $m \ge 2$; Problem **MI-20** remains **Open**.

What is proved in [`mi20_subquadratic_lee_whitepaper.pdf`](mi20_subquadratic_lee_whitepaper.pdf):

1. **Theorem 1 (Strict Infinite-Dimensional Hierarchy):** For every $1 < p < 2$, every $m \ge 2$, and every $n \ge 1$,
   $1 = C_{p,m}(1) < C_{p,m}(2) < \cdots < C_{p,m}(n) < C_{p,m}(n+1) < \cdots < C_{p,m}(\infty)$ over both $\mathbb{C}$ and $\mathbb{R}$, confirming the dimensional growth suggested in Hongsen Qiu's §5. By Xing Li's fixed-dimension concave-function transfer theorem (Theorem 1.1), the same strict hierarchy holds for concave-function Lee constants (**Corollary 1**). [Qiu, §5](https://arxiv.org/html/2608.17565v2#S5) · [Li, Theorem 1.1](https://arxiv.org/html/2608.25989v1).
2. **Theorem 2 (Infinite-Rank Obstruction on Hilbert Spaces):** On any infinite-dimensional separable complex or real Hilbert space $\mathcal{H}$, no tuple in $(\mathcal{S}_p(\mathcal{H}))^m$ containing even one finite-rank operator can attain $C_{p,m}(\infty)$; any attaining tuple must satisfy $\overline{\operatorname{ran}(S)} \subseteq \overline{\operatorname{ran}(A_k)}$ for all $k$.
3. **Theorem 3 (Universal $2\times 2$ Collapse & Exact Algebraic Constants):** For every $m \ge 2$ and every $p > 1$, $C_{p,m}(2) = C_{p,m}^{\mathbb{R}}(2) = C_{p,2}(2)$, with exact closed form $C_{3/2,m}(2) = \bigl(\frac{107+51\sqrt{17}}{256}\bigr)^{1/6}$ and monic cubic evaluation $z^3 - z^2 - 4z + 2 = 0$ at $p = 4/3$ giving $C_{4/3,m}(2) \approx 1.018302375431$ (strictly below Sidney Holden's certified lower bound $1.018371575$).
4. **Theorem 4 (Exact Zero-Float Rational Certificates):** Explicit small-integer $2\times 3$ pairs at $p \in \{3/2, 4/3, 5/4\}$ strictly surpassing $C_{p,m}(2)$, certified using pure Python standard-library rational/integer arithmetic without floating-point eigenvalue solvers.
5. **Proposition 5 (Superquadratic Phase-Transition Mechanism):** Kernel lifting extends to all $p \ge 2$. Every finite-dimensional tuple attaining the dimension-independent constant must satisfy $\ker(S) \cap \operatorname{ran}(H) \neq \{0\}$.

## Reproduction

```bash
# Zero-dependency exact rational certificates (Python 3 standard library only):
python3 -B -S references/diaz-mi20-2026-11-27/verify_exact_certificates.py

# Symbolic (SymPy), 105-digit (mpmath), and randomized lemma checks:
python3 references/diaz-mi20-2026-11-27/verify_all_math.py
```

## Audit notes

The Codex review checked the dimension-lifting and duality arguments and
reran all three exact rational certificates. The proof of Theorem 2,
step 1, uses the unitary from Lemma 3. For the singular vector convention
in that lemma, the unitary sends the left singular vectors of the trace
class operator to its right singular vectors. The manuscript reverses
the direction in that sentence.

The numerical optimization tables in Section 4 report achieved ratios.
Only the analytically evaluated entries in dimension two are certified
optima in those tables. The limiting estimates in Section 5 are
exploratory.

The review was informal and AI-assisted. It did not include external
human peer review or proof-assistant verification.
