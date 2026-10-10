# SP-14: endpoint cancellation and the first actual Wiener bound

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical/numerical contract, awaiting independent review before Lean implementation. Original negative target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially the weighted Wiener norm at lines 62–67, the endpoint-cancellation argument at lines 765–785, and the `g₀P₋` hypothesis/negative-frequency split at lines 1323–1328 and 1362–1368. Frozen audited prerequisites: normalized boundary factor `BaseExteriorFactor.lean` SHA `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd` and finite real Laurent background `FiniteLaurentBackground.lean` SHA `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b`.

## Literal coefficient norm and the regularized base factor

Fix the source value `α=1/8` and `β=1+α=9/8`. For a bilateral Laurent coefficient sequence `a : ℤ→ℂ`, define the possibly infinite weighted Wiener size

\[
 \|a\|_{\mathcal W^{9/8}}
   =\sum_{j\in\mathbb Z}(1+|j|)^{9/8}|a_j|.
\]

Here `|j|` is the integer absolute value and `|a_j|` is the complex norm. A Lean definition may use `ENNReal` or a finite-norm subtype; in either representation, the weight and bilateral index set must be literal. Theorems about finite size must not assume summability as a premise when claiming it for a source-constructed factor.

Let `c_n=binom(1/2,n)` from the frozen `baseCoeff` and set `d_n=c_n+c_{n+1}`. The exact recurrence and first coefficients are

\[
 (n+1)d_n=\tfrac32 c_n\quad(n\ge0),\qquad
 d_0=\tfrac32,\quad d_1=\tfrac38,\quad d_2=-\tfrac1{16}.
\]

The intended first Lean stage defines `regularizedBaseCoeff n : ℂ := baseCoeff n + baseCoeff (n+1)` and proves the recurrence, these endpoints, and the **unconditional** weighted summability

```lean
theorem summable_regularizedBaseCoeff_weighted :
  Summable (fun n : ℕ =>
    ((n + 1 : ℝ) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖)
```

An acceptable elementary majorant is `|c_n|≤C(n+1)^(-3/2)` and hence `|d_n|≤(3C/2)(n+1)^(-5/2)`; the weighted term is then at most a constant times `(n+1)^(-11/8)`, a convergent p-series. The exact recurrence for `c_n`, including `n=0`, already appears in the reviewed summability proof and can be made public or reproved. The numerical endpoint values above should be checked with rational arithmetic, not floating point.

The actual boundary Laurent factor

\[
 F(s)=(1+s)g_{0,\partial}(s)
     =s+\sum_{n\ge0}d_n s^{-n}
\]

must be proved as an equality of continuous circle functions using the normalized `baseExteriorFactor`, not declared as an independent formal symbol. Its coefficient sequence has `F_1=1`, `F_{-n}=d_n` for `n≥0`, and all other coefficients zero. In particular its literal Wiener norm is

\[
 \|F\|_{\mathcal W^{9/8}}
    =2^{9/8}+\sum_{n\ge0}(n+1)^{9/8}|d_n|<\infty.
\]

The `2^{9/8}` factor comes from frequency `+1`; there is no double count at frequency `0`. The frozen `FourierCoefficient` uses the real-interval normalization and sign, so the implementation must identify these claimed coefficients with that actual integral (or prove an equivalent coefficient uniqueness theorem for the absolutely convergent Laurent series).

## Separate endpoint condition and one of the five source bounds

Take `P₋` from the reviewed `negativeLaurent u pMinus`; its frequencies are exactly `−1,…,−u`. If `P₋(-1)=0`, prove a **finite real Laurent** factor `Q₋` with frequencies at most `−2` such that

\[
 P_-(s)=(1+s)Q_-(s)\quad\text{on }\mathbb T.
\]

For `u=0` or `u=1`, the endpoint condition forces `P₋=0` and one may take `Q₋=0`; these endpoints must be included. An explicit coefficient recurrence is `q₁=0`, `p_j=q_j+q_{j+1}` for `1≤j≤u`, with `q_{u+1}=0`; the endpoint condition is exactly the consistency condition at `j=u`. For the nonempty check `P₋(s)=t(s^{-1}+s^{-2})`, take `Q₋(s)=t s^{-2}`.

Consequently, the actual source product is `g₀P₋=FQ₋` on the circle. Prove its Fourier coefficients have no nonnegative frequency: `F` has maximal frequency `+1`, while `Q₋` has maximal frequency `−2`. Define the literal finite norm `‖Q₋‖_{𝒲^{9/8}}` from its coefficients and prove the weighted convolution bound with **constant one**

\[
 \|g_0P_-\|_{\mathcal W^{9/8}}
 \le \|F\|_{\mathcal W^{9/8}}\,\|Q_-\|_{\mathcal W^{9/8}}.
\]

The weight is submultiplicative because `1+|i+j|≤(1+|i|)(1+|j|)` and exponent `9/8` is positive. For the chosen exact threshold `γ=2^{-1000}` from the source's later explicit-parameters corollary, this one product has the derived sufficient condition

\[
 \|Q_-\|_{\mathcal W^{9/8}}
   < 2^{-1000}/\|F\|_{\mathcal W^{9/8}}
 \quad\Longrightarrow\quad
 \|g_0P_-\|_{\mathcal W^{9/8}}<2^{-1000}.
\]

The denominator is nonzero since `F_1=1`. This proves a **specific one** of the source's five smallness inequalities for a sufficiently small finite negative background; it does not assume the inequality as a free property of an arbitrary function. The source's two-level proposition itself assumes an unspecified sufficiently small `γ>0`; this gate alone does not prove that the chosen `2^{-1000}` suffices for that full proposition. The other four inequalities (`h-s`, `P₋`, `P₋/g₀`, `P₊`) and their simultaneous realization remain open.

## Scope and feasibility

The first stage is a coefficient recurrence plus a convergent p-series. The second requires exact Fourier identification of an absolutely summable Laurent product, finite endpoint division, and a weighted convolution inequality. These are substantial but finite/series-level tasks; no conformal map, Cauchy kernel, endpoint inverse, or Sobolev operator is hidden in the statement. Any Lean implementation may split the stages into separately frozen modules, each with its own final source/signature/kernel audit. No analytic extension or full SP-14 Target is claimed.
