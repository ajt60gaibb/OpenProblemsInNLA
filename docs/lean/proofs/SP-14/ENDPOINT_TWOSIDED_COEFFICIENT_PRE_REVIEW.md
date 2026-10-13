# SP-14: actual two-sided endpoint extension in weighted coefficient space

**Status:** source-locked mathematical and exact-numerical pre-implementation contract; independent review required before Lean source. **Author:** `/root/sp14_base_proof`, 10 October 2026.

The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical construction is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Lemma “The square-root extension of the analytic projection,” lines 851–900. The exact finite Fourier integral and negative matrix are in `EndpointFiniteMatrixSchur.lean` SHA-256 `0b8c3b6c2647a2f955a638993b0560343cc101f10adb8df16ad4fd096800de3b`. The literal one-sided weighted coefficient carrier is `SobolevCoeff r = lp (fun _ : ℕ => ℂ) 2` in `WeightedSobolevPhysical.lean` SHA-256 `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109`. The completed but independently unaudited negative CLM source is `EndpointNegativeOperator.lean` SHA-256 `16685a4f52b47911d79fc79b78cbdd9117e3efcb914e5102e0b068da118442b1`; this contract depends on its final imported audit before implementation.

Fix `0<r<1` and the **literal** `C_r=endpointSchurConstant r=1+1/r+1/(1-r)`. The positive weighted sequence of the canonical extension is exactly the input `y`; the negative weighted sequence is exactly `endpointNegativeOperator r hr hr1 y`. Thus the positive mode `p=k≥0` has physical Fourier coefficient `physicalCoeff r y k`, while the negative mode `p=-(t+1)` has weighted coefficient `endpointNegativeOperator ... y t`. The mode sets are disjoint and exhaustive: zero is positive (`k=0`), and the first negative mode is `-1` (`t=0`). No duplicated zero mode or one-index shift is allowed.

## Exact Lean surface

Use the finite two-block Hilbert sum with the **ℓ² product norm**, for example

```lean
noncomputable abbrev TwoSidedCoeff (r : ℝ) :=
  lp (fun _ : Bool => SobolevCoeff r) 2

noncomputable def endpointTwoSidedCoeffOperator
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    SobolevCoeff r →L[ℂ] TwoSidedCoeff r
```

Choose and document the block orientation `true = nonnegative`, `false = negative` (or the opposite consistently). Prove the exact coordinate identities for every `y`:

```lean
endpointTwoSidedCoeffOperator r hr hr1 y true = y
endpointTwoSidedCoeffOperator r hr hr1 y false =
  endpointNegativeOperator r hr hr1 y
```

and the exact norm-square identity

\[
 \|\texttt{endpointTwoSidedCoeffOperator}(y)\|^2
   = \|y\|^2+\|\texttt{endpointNegativeOperator}(y)\|^2.
\]

Then prove both the pointwise and operator norm bounds

\[
 \|\texttt{endpointTwoSidedCoeffOperator}(y)\|
 \le \sqrt{1+C_r^2}\,\|y\|,
 \qquad
 \|\texttt{endpointTwoSidedCoeffOperator}\|
 \le \sqrt{1+C_r^2}.
\]

An equivalent public Lean type is acceptable only if its norm is proved to be this exact orthogonal sum and its mode orientation is explicit. A default `Prod` maximum norm is not acceptable for the displayed identity. The operator is unconditional on the actual Fourier-derived negative CLM; an abstract pair or assumed norm hypothesis does not satisfy this gate.

## Mathematical proof and exact checks

The map `y ↦ (y,Ty)` is complex linear because both blocks are complex linear. The `lp 2` norm on the two-element index is the square root of the sum of the two block norms squared. The already audited negative estimate gives `‖Ty‖≤C_r‖y‖`, hence the exact displayed square and square-root bounds. This is the source's bounded two-sided extension in a coefficient Hilbert model; the manuscript writes an unspecified constant `C_r` for the **total** norm, so its constant may absorb our explicit `sqrt(1+C_r²)`.

For `y=0`, both blocks and the norm vanish. The empty polynomial is included. For `r=1/2`, `C_r=1+2+2=5`, so the explicit total bound is `sqrt(26)` and its squared bound is `26`. The `k=0` positive mode and `t=0` negative mode are separate; the latter is physical mode `-1`. These are exact symbolic checks, not floating-point tests.

This gate does not yet identify the two-block coefficient Hilbert space with a *function* in the source's circle `H^r(𝕋)`, prove `Π₊Ey=y` in a function-level projection, construct the inverse `V`, show pointwise vanishing at `-1`, or establish actual background-dependent inverse estimates, nonlinear stage, jet-vector existence, both-sided nonextension, canonical gap, or the frozen negative Target. Those require separate exact mathematical contracts and independent review. No Lean source for this gate before its own pre-review; freeze any implementation for separate imported LeanCert source/signature/kernel audit before aggregate import.
