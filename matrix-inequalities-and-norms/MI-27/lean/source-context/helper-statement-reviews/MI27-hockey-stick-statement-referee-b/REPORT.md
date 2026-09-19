# MI-27 hockey-stick substitution: independent pre-body statement review

**Verdict: APPROVE all eight proposed helper headers. No blocking mathematical or statement-fidelity finding.**

Reviewer: `/root/nr04_mf14_final_referee_b`, independent nonauthor AI agent. This is a bounded second mathematical/statement review before implementation of the new headers, not a proof-body review or compilation claim. I authored no MI-27 definition, header, or proof; ran no Lean/Lake/Comparator; changed no development source; and claim no completed C11, complete MI-27 verification, or count increment.

The exact reviewed document is `development/MI27-C11-referee-a-v1/HOCKEY-STICK-SUBSTITUTION-STATEMENTS.md`, SHA256 `27377238478a6dd0254cb3a2a3b9574e50f0c6d17c551336314cd01a26280b3e`, copied unchanged as `REVIEWED-STATEMENTS.md`. I checked its eight new headers, the final reproduced C11 header, the earlier pencil-integral and scalar statement plans, the actual unchanged semantic definitions, relevant existing finite-integrability/zero-tail interfaces, and the stated pinned Mathlib API signatures.

The approved new headers are:

- `c11_tracePos_smul_nonneg`
- `c11_pencil_tracePos_zero_unit_interval`
- `c11_change_variable_pencil_positive`
- `c11_change_variable_pencil_negative`
- `c11_pencil_integrand_positive_substitution`
- `c11_pencil_integrand_negative_substitution`
- `c11_relative_entropy_hockey_stick_Ioi`
- `c11_integral_Ioi_eq_interval_of_zero_tail`

`tracePos` is the real part of the actual trace of the spectral positive part, and `E γ X Y = tracePos (X − γY)`. Nonnegative scalar homogeneity follows from `max(a x,0)=a max(x,0)` for `a≥0`, followed by trace linearity. The statement correctly includes `a=0` and empty matrices (`n=0`). No positive definiteness or nonzero spectrum is needed. For positive semidefinite X,Y and 0≤t≤1, the pencil equals `(1−t)X+tY≥0`; its negative has zero positive part, including singular matrices, repeated/zero eigenvalues, and both endpoints. Multiplying this zero by the totalized weight at t=0 or t=1 introduces no integral contribution.

For γ>1, `T(γ)=γ/(γ−1)=1+1/(γ−1)` maps (1,∞) bijectively onto itself, is its own inverse, and has derivative `−1/(γ−1)^2`. It reverses orientation, but the **set** integral substitution correctly uses the absolute Jacobian, with no leftover minus sign. `N(γ)=−1/(γ−1)` maps (1,∞) bijectively onto (−∞,0), has inverse `1−1/t`, and derivative `1/(γ−1)^2`. Its orientation is increasing. Thus both displayed transformations use exactly the positive factor `1/(γ−1)^2`. No singular endpoint belongs to either substitution domain.

The arbitrary-f quantification in the two change-of-variables headers is justified by the actual Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`: `MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul` and `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` take a measurable domain, derivatives within that domain and injectivity, then an arbitrary integrand. They do not require a separate measurability or integrability assumption on f. The supplied integrability equivalence therefore makes the stated totalized Bochner identities meaningful also outside the integrable case. For these maps, the open domains are measurable, derivatives exist at every domain point, and the inverse formulas prove injectivity and the exact images.

Write `d=γ−1>0`. For T, `−(X+T(Y−X))=(X−γY)/d`, `|T|=γ/d`, and `T−1=1/d`, so the pencil weight is `d^3/γ`. Homogeneity contributes `1/d` and the absolute Jacobian `1/d^2`; the result is exactly `E γ X Y / γ`. For N, `−(X+N(Y−X))=(Y−γX)/d`, `|N|=1/d`, and `N−1=−γ/d`, so the weight is `d^3/γ^2`. The same other factors yield exactly `E γ Y X / γ^2`. These are scalar linear-combination identities; no matrix factors are commuted. Hermitian hypotheses suffice for these two pointwise statements.

The general improper formula correctly retains `relEntropy X Y − trR(X−Y)`. It follows from the previously reviewed full-real-line pencil integral by restriction to the two tails, both proved substitution integrability equivalences, zero on the central closed interval, and integral additivity. Singleton endpoints are Lebesgue-null. The proposed conclusion asserts integrability as well as equality, so no illicit interchange or addition of divergent integrals is concealed. The unrestricted positive-definite inputs need not have equal traces or commute. Scalar checks X=2,Y=1 and X=1,Y=2 give respectively `2 log 2−1` and `1−log 2`, confirming the correction sign and which denominator belongs to each tail.

For the cutoff lemma, pinned `intervalIntegral.integral_Ioi_sub_Ioi` has precisely the stated prerequisites: integrability on Ioi(1) and 1≤R. Its subtraction of the Ioi(R) tail reduces to the proposed equality because that tail vanishes. Requiring zero at γ=R is stronger than needed but is available from the existing Loewner helper. R=1 is fully included: the whole Ioi(1) integrand is zero, while the interval integral from 1 to 1 is zero. No strict cutoff premise or limiting argument is silently added.

The final C11 header reproduced in the plan agrees with the frozen `relative_entropy_finite_hockey_stick` contract (Challenge SHA256 `1cacb3aa3088860016b9d121904677d56c6c8e6025de9eeaf262957c2bc0d640`), including both original two-sided Loewner bounds, the supplied R≥1, the two denominators and the conjunction with interval integrability. `StrictDensity` is exactly positive definiteness and literal complex trace one. Consequently trace linearity cancels `trR(ρ−σ)` without any extra entropy or support premise. The existing finite-integrability and two-sided zero-tail interfaces have the needed hypotheses, including equality at the cutoff. At R=1 the two order bounds force equality of the densities, consistently giving zero relative entropy. No larger replacement cutoff, commutativity assumption, assumed entropy integral, alternate definition or C12 premise is introduced.

Implementation must still establish the exact proposed statements and pass the coordinator's actual serial local compilation and trust checks. The pre-body approval supplies no evidence of those future runs or of final GitHub Comparator acceptance.
