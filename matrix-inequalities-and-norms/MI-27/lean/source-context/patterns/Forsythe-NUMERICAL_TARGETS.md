# Algebraic Hopf certificate

The numerical export in [Solution.lean](Solution.lean) proves the certificate
from Section C.3 of the [manuscript](https://arxiv.org/abs/2609.04659):

```lean
ProofProject.restartFourAlgebraicHopfCertificate :
  ProofProject.RestartFourAlgebraicHopfCertificate
```

Its data and propositions are defined in
[ProofProject/Definitions.lean](ProofProject/Definitions.lean). The proof is
assembled in
[RestartFourAlgebraicHopfCertificateCertified.lean](ProofProject/RestartFourAlgebraicHopfCertificateCertified.lean).

## Exact input data

Every decimal in C.3 is interpreted as the corresponding exact rational. The Lean declarations expand to the following values:

- `restartFourC = 31355365301369736 / 100000000000000000`.
- `restartFourPRoot`, in its fixed order, is
  `(-3812196375334383/10^15, -3408184613601878/10^16, 15054785540322202/10^16, 2190808973956946/10^15)`.
- The three fixed roots in `restartFourQFixedRoot` are
  `(-23304189906225/10^13, 6733921795528344/10^16, 4323444838404325/10^15)`; the fourth root of `Q_q` is the parameter `q`.
- `restartFourP = ∏(X-r)` and `restartFourQ q = (X-q)∏(X-r)` are monic quartics over `ℝ`; `restartFourFminus q = P Q_q - C` and `restartFourFplus q = P Q_q + C`.
- The closed parameter domain is
  `restartFourQInterval = [-1851888497035/10^12, -1851888497033/10^12]`.
- The closed recovery-root domain is
  `restartFourAlphaInterval = [2952193/10^7, 29521955/10^8]`.
- In one-based source notation the six core roots of `F_-` have indices `(1,2,4,5,7,8)`, the removed roots have indices `(3,6)`, and the two selected external roots of `F_+` have indices `(2,7)`. The Lean `Fin` arrays record exactly the corresponding zero-based indices `(0,1,3,4,6,7)`, `(2,5)`, and `(1,6)`.

The predicate characterizes the eight roots by strict order and exact polynomial factorization. Rational isolating collars are used within the proof.

## Certificate statement

`RestartFourAlgebraicHopfCertificate` asserts the existence of data `d` satisfying `IsRestartFourAlgebraicHopfCertificate d`. The latter contains the following assertions:

| Component | Exact domain | Exact assertion |
|---|---|---|
| Root and critical branches | `q ∈ restartFourQInterval`, including both endpoints | The eight minus roots and eight plus roots are strictly ordered exact factorizations of `F_-(·,q)` and `F_+(·,q)`. Both root maps, the critical recovery root `α(q)`, and the two amplitudes are analytic on a neighbourhood of the closed `q` interval. The factorization `F_- = H Δ` uses exactly the six core and two removed labels above. |
| Critical solution | `q` on the same closed interval; uniqueness over `a ∈ restartFourAlphaInterval` and all `c : Fin 2 → ℝ` with `c_g > 0` | `α(q)` lies in the closed alpha interval, `c(q)` solves the exact normal-balance and two tangent-rate equations `RestartFourCriticalEquations`, and every positive solution on that domain equals `(α(q),c(q))`. |
| Tangent construction | `(q,a) ∈ restartFourQInterval × restartFourAlphaInterval`; each selected external root | The tangent map is analytic on a neighbourhood of the closed product. `IsRestartFourTangentConstruction` states the exact quotient/remainder, divided-kernel, and coefficient polynomial identities (C.3.7)--(C.3.10), including degree bounds and all denominator nonvanishing required on this domain. |
| Phase weights and nodes | Every `q` on the closed interval, evaluated at `a=α(q)` | The six `P`-sheet and six `Q`-sheet weights defined by (C.3.5) each sum exactly to `1` and each exceed `2^-19`. Every selected centered core and external node lies strictly between `-4` and `5`. The two amplitudes satisfy `c_- > 2^-15` and `c_+ > 1/4`. |
| Linearization | Every `q` on the closed interval | The exact `7 × 7` scalar Jacobian has characteristic polynomial `(λ+1)(λ-1)(λ-2)[θ²-τ(q)θ+K_θ(q)]`, with `θ=λ(λ-1)`, using the exact formulas (C.3.17a)--(C.3.21). Its theta-discriminant is strictly less than `-277/5 = -55.40`. The derivative of the Hopf functional lies strictly between `10989/100 = 109.89` and `5541/50 = 110.82`. |
| Unique Hopf point | `q_* ∈ restartFourQInterval` | The Hopf functional vanishes exactly when `q=q_*`; `q_*` is farther than `2^-41` from each interval endpoint. The exact theta identities define `ω_*`, with `93/25 = 3.72 < ω_* < 931/250 = 3.724`. The crossing magnitude `abs(-H'(q_*)/(1+4ω_*²))` is strictly greater than `97/50 = 1.94`. |
| Visibility | The real and imaginary parts of every nonzero `±iω_*` eigenvector of the exact Jacobian | At least one recovery-root component is nonzero. This is the precise real-coordinate version of the source's visible Hopf mode. |

## Use in the classification

The restart-two and restart-three proofs are analytic. For restart lengths
at least four, the proof combines this finite algebraic certificate with
analytic degree elevation, local rescaling, periodic-orbit construction,
shadowing, positivity, and reconstruction as exact CG trajectories.

The spectral calculation reduces to a quadratic in `θ = λ(λ−1)` after
factoring out `(λ+1)(λ−1)(λ−2)`. The critical branch is expressed through one
recovery root and two amplitudes. Polynomial identities, root bounds, and
interval inequalities are established by Lean proofs.

Proposition C.1.2's particular `ε₀`, `M`, and `N` construction is outside the
configured theorem set. The main counterexample theorem uses the qualitative
existence results of C.14–C.18. The Lean proofs use no external data files or
Python computations as premises.
