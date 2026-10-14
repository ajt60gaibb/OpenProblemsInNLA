# SP-14 finite inverse Fourier gate: independently reviewed declaration-name correction

The aggregate import found that `EndpointFiniteRealizationNegative.lean` already exports `NLA.Proofs.SP14.endpointFiniteInverse_fourier_neg`. That existing theorem concerns the negative Fourier coefficients of the **product** `endpointBaseSymbol * endpointFiniteInverse`, with finite-support and `1/2<r<1` premises. The new reviewed theorem concerns the **inverse polynomial alone**, whose strictly negative coefficients vanish and which needs no support or `r` premise. Both are mathematically distinct and both must remain available.

Before changing the new source, I reviewed the exact replacement name `endpointFiniteInversePolynomial_fourier_neg` for the same proposed public statement:

```lean
theorem endpointFiniteInversePolynomial_fourier_neg (r : ℝ)
    (y : SobolevCoeff r) (N t : ℕ) :
    FourierCoefficient (endpointFiniteInverse r y N)
      (-((t + 1 : ℕ) : ℤ)) = 0
```

No parameter, normalization, source quantity, or conclusion changes. The canonical source and frozen Target remain untouched. The new name disambiguates `V_N` from `g₀V_N`; the original theorem keeps its published name. The implementation must be recompiled and separately imported under this exact signature before aggregate import.
