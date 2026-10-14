# SP-14 actual base-jet Fourier matrix: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical review before Lean implementation. The exact frozen `Target` is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Proposition “Odd-symbol pencil and its jets” and the finite restoration packet section. This is the actual Fourier/Toeplitz identification required by the approved constructive base-pencil contract `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md` (SHA `bbcb1bfe...`). It uses the original interval-integral `FourierCoefficient` definition and does not postulate a Fourier pattern.

## Definitions and exact coefficient scope

For `m q : ℕ`, `v : Fin q → ℂ`, define the actual continuous circle symbol and upper Toeplitz coefficient matrix

```lean
noncomputable def baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) : Circle → ℂ :=
  fun z => baseExteriorSymbol z + restoredNegativePacket m q v z

noncomputable def baseJetG (m q : ℕ) (v : Fin q → ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => baseG m i j +
    ∑ d : Fin q, if j.val = i.val + (m - d.val) then v d else 0
```

Assume `2*q ≤ m+1` throughout the selected-section theorems; this gives `d<m` for every `d:Fin q` (unless `q=0`), so the added modes are strictly negative in `g` and strictly above the diagonal of `G`. The exact current-order restoring term has circle frequencies `1−2(m+1+r)`, `0≤r≤m`; all are below `−2m`, whereas the entries of `Toeplitz a (2m+1)` use only frequencies `−2m,…,2m`. Thus **only the `K_m` part** of `restoredNegativePacket` is invisible at this order. The raw `negativeL` part remains visible and supplies the `v` entries.

For every integer `p` with `p≤m`, the frozen coefficient should be proved directly from the reviewed mode integral and finite-sum linearity:

\[
\widehat{a_v}(1-2p)
=\begin{cases}c_p,&p\ge0,\\0,&p<0,\end{cases}
+\sum_{d=0}^{q-1}\mathbf 1_{\{p=m-d\}}v_d,
\qquad c_p=\binom{1/2}{p}.
\]

Here `a_v=baseJetSymbol m q v`. The formula is asserted only for `p≤m`: the restoring packet may contribute for `p=m+1,…,2m+1`, while `p≤m` is the uniform safe range. If `q=0` or `negativeL m q v (-1)=0`, its contribution vanishes, and the displayed formula may also hold beyond that range. Even-frequency coefficients vanish for **all** integer frequencies because both the base and each packet have odd circle modes. Prove these public Lean statements:

```lean
theorem continuous_baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) :
    Continuous (baseJetSymbol m q v)

theorem oddSupport_baseJetSymbol (m q : ℕ) (v : Fin q → ℂ) :
    OddFourierSupport (baseJetSymbol m q v)

theorem baseJetSymbol_fourier_selected (m q : ℕ)
    (hq : 2 * q ≤ m + 1) (v : Fin q → ℂ) (p : ℤ) (hp : p ≤ m) :
    FourierCoefficient (baseJetSymbol m q v) (1 - 2 * p) =
      (if 0 ≤ p then baseCoeff p.toNat else 0) +
        ∑ d : Fin q, if p = (m : ℤ) - (d.val : ℤ) then v d else 0

theorem oddB_baseJetSymbol (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddB (baseJetSymbol m q v) m =
      (baseJetG m q v).submatrix id Fin.succ

theorem oddC_baseJetSymbol (m q : ℕ) (hq : 2 * q ≤ m + 1)
    (v : Fin q → ℂ) :
    oddC (baseJetSymbol m q v) m =
      (baseJetG m q v).submatrix Fin.castSucc id
```

The `hp` condition is written as `p ≤ (m : ℤ)` in Lean if needed. In the odd `B` block, `p=(j+1)-i` ranges from `1−m` to `m`; in the odd `C` block, `p=j-i` ranges from `1−m` to `m`. The entries match the row-minus-column convention of frozen `Toeplitz` exactly: `oddBᵢⱼ` uses circle frequency `2i−(2j+1)=1−2((j+1)-i)`, and `oddCᵢⱼ` uses `(2i+1)−2j=1−2(j-i)`. No conjugation or reversed Toeplitz convention appears.

## Proof and endpoints

Use the independently reviewed `baseExteriorSymbol_fourier_pattern`; expand `negativeL m q v` as the finite circle mode sum with exponent `1+2(d−m)`, then use `FourierCoefficient_circle_mode` and interval-integral addition for continuous summands. At `p≤m`, the restoring term's exponents `1−2(m+1+r)` cannot equal `1−2p`, so its integral is zero. The reviewed theorem `toeplitz_add_restoration_invisible` supplies an alternative direct proof for block entries, but it must not be misapplied to the full `D_v`. The reindexing to `baseJetG` is finite integer arithmetic, including the `j<i` case where both the base coefficient and added high-superdiagonal term vanish.

At `q=0`, the sum is empty, `baseJetSymbol=baseExteriorSymbol`, and `baseJetG=baseG`; both block identities reduce to the existing reviewed base parity blocks. At `m=0`, the size hypothesis forces `q=0`; `oddB` has shape `1×0`, `oddC` `0×1`, and the coefficient theorem at `p≤0` includes negative p without an invalid natural cast. At `m=1,q=1`, the added raw correction occupies `G₀₁` exactly, while the restoring modes begin at circle frequency `−3` and do not enter `T₃`. The theorem does not claim the corrected symbol is the final counterexample or that arbitrary target jets are solved.

## Next algebraic obligation

After this actual Fourier matrix bridge is independently reviewed, a separate source-locked proof must show `baseJetG = baseG+E`, `E²=0`, `baseG*E=E*baseG`, and evaluate the upper-right adjugate corner of `G²−(1+t)U` as the explicit finite polynomial in `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md`. The already approved generic cofactor identity then gives the actual `oddJetPolynomial` formula and the real triangular solve. This Fourier bridge alone has no vector existence or `Target` consequence.
