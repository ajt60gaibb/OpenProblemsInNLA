# MI-27 C12: independent pre-body statement review

**Verdict: APPROVE all nine exact helper headers and the unchanged reproduced C12 contract. No blocking finding.**

Reviewer: `/root/nr04_mf14_final_referee_b`, independent nonauthor AI referee. Exact packet: `development/MI27-C12-root-v1/STATEMENTS.md`, SHA256 `0dfdccc245cc3dae033c924a695e1dbc7610ab87fcd19c6d1acdb64da27e58ae`. I read the complete statement packet against the actual frozen `chi`, `entropy`, `relEntropy`, `E`, `StrictDensity`, and scalar kernel definitions and the frozen Challenge. I wrote no MI-27 source or proof, ran no compiler or Comparator, and make no completed C12 or MI-27 verification claim.

The nine approved headers are `c12_mixture_strict_density`, `c12_chi_relative_entropy`, `c12_E_mixture_forward`, `c12_E_mixture_reverse`, `c12_mixture_cutoffs`, `c12_integral_truncate_zero_tail`, `c12_change_variable_forward`, `c12_change_variable_reverse`, and `c12_relative_entropy_mixture_finite`.

Positive mixture density follows from the positive real weights, positive definiteness, and literal complex trace one. The unrestricted `chi` identity is valid for arbitrary matrices and arbitrary real a,b: distribute multiplication and trace across `M=aρ+bσ` in `tr(M logM M)`. It needs neither a+b=1 nor positivity, nor linearity of the logarithm, nor a commutation of matrix factors. The definitions are totalized, so non-Hermitian inputs do not undermine this algebraic identity.

Set `D=b+aγ`. For γ≥1 and a,b>0, D>0 and `ρ−(γ/D)M=(b/D)(ρ−γσ)`. Positive-part homogeneity gives the proposed forward identity without requiring a+b=1. Likewise `M−(a+bγ)ρ=b(σ−γρ)` proves the reverse identity under just b≥0; b=0, negative a, and arbitrary γ are correctly included. The factor being pulled through `tracePos` is never negative.

With a+b=1 and R≥1, `b+aR=1+a(R−1)` and `a+bR=1+b(R−1)`. Thus the proposed L=R/(b+aR) and U=a+bR both lie in [1,R]. The supplied bound ρ≤Rσ gives `(b+aR)ρ≤R M` and hence ρ≤L M; σ≤Rρ gives M≤Uρ. Positivity of M and ρ then makes the same original R a common two-sided cutoff for (ρ,M). No larger replacement R or unmentioned Loewner bound is needed.

Each continuous C11 integrand must be truncated separately, to L for `E(v,ρ,M)/v` and U for `E(v,M,ρ)/v²`, before substitution. Their zero tails follow from the corresponding exact Loewner inequalities, including equality at the cutoff. The forward map γ/(b+aγ) increases from 1 to L with derivative b/(b+aγ)². The reverse map a+bγ increases from 1 to U with derivative b. Both closed interval images are exact and every denominator is positive. Combining the E identities with these derivatives produces precisely the displayed b² weights: `b²/[γ(b+aγ)²]` and `b²/(a+bγ)²`.

The generic reverse change-of-variable lemma correctly omits positivity of a: b>0 and a+b=1 still give `a+bγ=1+b(γ−1)≥1` on [1,R]. The generic truncation lemma assumes sufficient compact-interval continuity and a vanishing tail. Both lemmas include zero-length intervals. At R=1, L=U=1 and all integrals are zero; the original two order bounds also force ρ=σ. No singular endpoint, limit argument, strict R>1 premise, or omitted integrability hypothesis is present.

After swapping (ρ,a) with (σ,b) and multiplying the two entropy identities by a and b, the coefficient of E(γ,ρ,σ) is `ab²/[γ(b+aγ)²]+ba²/(b+aγ)²=ab/[γ(b+aγ)]`. The other coefficient is `ab²/(a+bγ)²+ba²/[γ(a+bγ)²]=ab/[γ(a+bγ)]`. These are exactly the frozen `kernelAB` and `kernelBA`, respectively. The supplied continuous-on-compact hypotheses give the needed interval integrability. Repeated spectra and noncommuting matrices remain covered.

The final `weighted_entropy_finite_kernel` header matches the frozen C12 contract, including n≥1, both strict densities, the original R and both original order bounds, a,b>0, a+b=1, the two exact coefficients, and the conjunction with interval integrability. C11 must become an internally proved import; this review neither assumes it as an axiom nor reports its unfinished/future execution as successful. Source bodies and actual local trust checks remain separate obligations.
