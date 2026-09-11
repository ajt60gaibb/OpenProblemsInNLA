# Independent review: Gamma auxiliary counterexamples

Reviewer: independent sub-agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Verdict: PASS for refuting the upper-mode assertion in Hallman's Conjecture 1 and the upper-inflection assertion in Conjecture 2. Neither RA-12 nor RA-13 is resolved.** No substantive proof gap was found in the supplied note. This is analytic review of a candidate, not formal verification, peer-reviewed acceptance, or a priority finding.

## Material actually reviewed and identity

Read the full original `04_gamma_auxiliary_counterexamples.tex` and `common_preamble.tex` under `.cache/colbrook-transfer-submission/nla_submission/manuscripts/`, every proof and numerical claim, and the exact canonical RA-12 and RA-13 READMEs. No proof or canonical text was edited.

SHA-256 is over the full UTF-8 text with CRLF replaced by LF, **without trimming** whitespace or final newlines. The original files already used LF here.

| Full original | Normalized bytes | SHA-256 |
| --- | ---: | --- |
| `04_gamma_auxiliary_counterexamples.tex` | 6707 | `222de12c79ca779329500977da68fb58ca3f0a10a0ae11058550db303ac8fe8b` |
| `common_preamble.tex` | 1105 | `8b784fe6ac56151b19d51534474560bf45df7b278015cd0c834569e2550fada4` |

## Primary-source scope check

Directly checked Definitions 9–10, Theorems 2 and 4, Conjectures 1–2, and Theorems 6–7 with Conjectures 3–4 in [Hallman, arXiv:2411.15454v1](https://arxiv.org/html/2411.15454v1). The first two conjectures bound extrema over augmented densities; the later two concern final extremal trace-tail chains. The augmenting exponential variables must have distinct coefficient indices, but those coefficients need not have distinct values. The manuscript's `j=1, k=2` is therefore legal. Centering in the absolute auxiliary family subtracts the mean of the base variable, not the augmented variable. The manuscript uses precisely that centering.

The version-qualified page was used for the numbered definitions and formulas. This review does not infer priority or a changed arXiv version from the generated date printed inside the HTML.

## Distribution and calculus

PASS. With shape–rate convention, `G_1+G_2` has law Gamma(1,1), and `(G_3+G_4)/2` has law Gamma(1,2). Adding the two independent Gamma(1,1) increments to the first part gives the independent sum Gamma(3,1)+Gamma(1,2). The base mean is `4*(1/2)` weighted by `(1,1,1/2,1/2)`, hence `3/2`; the variance is `(1/2)(1+1+1/4+1/4)=5/4`.

The convolution factors cancel their factor 2 exactly:

`p(x)=exp(-x) integral_0^x (x-y)^2 exp(-y) dy`

`=exp(-x)(x^2-2x+2)-2exp(-2x)` for `x>0`.

Ordinary differentiation gives precisely

`p'(x)=-exp(-x)(x-2)^2+4exp(-2x)` and

`p''(x)=exp(-x)(x-2)(x-4)-8exp(-2x)`.

The convolution supplies positivity and normalization of the density; they are not assumed solely from a possibly cancelling exponential expression.

## Mode counterexample

PASS. Normalizing the base sum by `2/3` gives mean one, coefficient vector `(2/3,2/3,1/3,1/3)`, and scale `2/3`. The allowed parameters are `alpha=1/2`, `beta=1`, `mu=3/2`, with `mu>=alpha`. The augmented variable is exactly `Y'=(2/3)Y`. Thus its claimed endpoint `5/3` corresponds to `5/2` for `Y`.

The sign at that point reduces to `exp(5/2)<16`. The proof's elementary certificate is valid: `e<3` gives `exp(5/2)<9sqrt(3)<16`, and the last comparison is equivalent to `243<256`. One can justify `e<3` immediately from its factorial series. Hence `p'(5/2)>0` strictly.

A positive derivative at one point would not alone locate the global mode, so I checked the separate uniqueness argument. On `0<x<=2`, strict convexity gives `2exp(-x/2)>2-x>=0`, whose squares prove the positive derivative. For `x>2`, the derivative has the sign of `2exp(-x/2)-(x-2)`. The first term strictly decreases and the second strictly increases, producing exactly one zero and a change from positive to negative. The density vanishes at the left boundary and at infinity. The zero is therefore the unique global positive mode and lies above `5/2`.

Solving this equation gives `2+2W(e^-1)`, with the nonnegative real branch unambiguous. Independent numerical bisection reproduced `2.556929085522146`, and scaling gave `1.7046193903480973>5/3`. The numerical root is corroboration only; the analytic sign and uniqueness establish the result.

Only the upper part of Conjecture 1 is refuted. The note does not address its lower-mode assertion.

## Inflection counterexample

PASS. For the unnormalized base sum, the scale bound is 1 and variance is `5/4`, so `lambda=1`, `phi=sqrt(5)/2`. The required parameter inequality is satisfied because `phi/sqrt(alpha)=sqrt(5/2)>1`. Selecting the first two distinct indices gives the centered augmented variable `Y-3/2`. Its alleged upper endpoint is `1+sqrt(5/4+1)=5/2`, corresponding to `x=4` for the uncentered density.

The analytic signs are exact: `p''(4)=-8exp(-8)<0`; `p''(5)=exp(-10)(3exp(5)-8)>0`, since `exp(5)>1+5=6`. Moreover, for `x>4` the equation for a zero is `(x-2)(x-4)exp(x)=8`. The left side increases strictly from zero to infinity: both positive polynomial factors increase, as does the exponential. The unique zero has negative second derivative before and positive second derivative after it. It is consequently a genuine inflection point, not merely a zero of the second derivative without curvature change.

The zero lies in `(4,5)`, and subtracting `3/2` places it in `(5/2,7/2)`, strictly outside the asserted bound. Independent bisection reproduced `4.066357206046174`, centered value `2.566357206046174`. Independent numerical signs at the three diagnostic points were approximately `p'(2.5)=0.00643054`, `p''(4)=-0.00268370`, and `p''(5)=0.01985064`; the exact signs above are the proof.

## Why the canonical trace questions remain open

RA-12 requires two explicit tail comparisons, valid for every PSD matrix and integer sampling number once `epsilon>=2/(m mu)`. RA-13 requires its own two comparisons for every symmetric matrix once epsilon exceeds its displayed absolute threshold. Neither asks that all the intermediate augmented densities have their mode or every inflection point below that threshold.

The manuscript exhibits no matrix and tolerance violating either canonical probability chain and proves no implication from failure of a density-location bound to failure of those chains. A sufficient device for proving all intermediate comparisons can fail while the final extremal comparisons remain true. The broad-family supremum cannot simply be substituted for the least threshold needed for the endpoint comparisons.

The Gaussian connection does hold: Gamma(1/2,1) is distributed as half the square of a standard normal, so the positive weighted base sums can be realized by one-sample Gaussian quadratic forms after scaling their eigenvalues. That observation supplies admissibility in the auxiliary setting; it does not identify a failed final tail comparison.

## Exact remaining questions and disposition

- **Auxiliary Conjecture 1:** its upper assertion is false for the supplied parameters if this candidate is accepted; its separately stated lower assertion is not settled by this note.
- **Auxiliary Conjecture 2:** its asserted upper inflection bound is false for the supplied parameters if this candidate is accepted.
- **RA-12:** are both comparisons in its complete probability chain valid for all its inputs at every `epsilon>=2/(m mu)`? The present note supplies neither a proof nor a counterexample. Retain the canonical open status and label this only related auxiliary evidence.
- **RA-13:** are both comparisons in its probability chain valid for all inputs at every `epsilon>=2lambda/m+sqrt(2phi^2/m+(2lambda/m)^2)`? Again unresolved by this note; retain the canonical open status. The canonical statement's disclosed source-prose inconsistency is immaterial to these auxiliary counterexamples.
- No exact sharp replacement for either auxiliary bound, random-estimator performance claim, or priority over subsequent literature is proved here. Those are not missing steps in the two actual counterexamples.
