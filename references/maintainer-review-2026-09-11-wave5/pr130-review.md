# Independent mathematical audit: PR130 / IE-04

Exact reviewed head: `397c70a40e8ee785201800d20f798c7d9b73c22f`, read-only checkout `/private/tmp/nla-pr130`.

**Verdict: PASS — complete negative resolution of the canonical universal exponential tail. No mathematical blockers found.**

Read the complete 268-line canonical solution and original problem. The submitted AI review was not used as authority. This audit covers the analytic proof, original-target preservation, and source attribution; root handles integration, CI, and publication artifact QA.

## Original target and quantifiers

The canonical README asks for one universal pair c1,c2>0 valid for all n, deterministic real centers of spectral norm at most one, 0<sigma<=1, and every real x>=1. The proposed counterexample uses I_n, sigma=1, which are admissible regardless of any additional nonsingularity requirement for the center. The high-growth matrix W_n is the center of a rare event in perturbed-input space, not the deterministic smoothed center; its norm need not be at most one.

The complete README from `## Context and notation` onward is byte-identical to origin/main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. SHA-256 of the unchanged suffix: `a4c427fe31d5b5977f80e6c2c390a64ee9425daea520a95ce5ed05bbcade5c0a`. IE-04 retains its ID, canonical path, and full original question. “Solved negatively” answers the full universal yes/no target. The scope at solution lines 43–45 and 260 correctly leaves other high-probability or restricted-range statements unclaimed.

## Independent analytic checks

- **Base high-growth input (solution lines 49–86):** In each active nonfinal pivot column, W_n has diagonal 1 and all competitors -1/2. Its zero upper entries in other nonfinal columns keep the triangular pattern invariant. Every remaining final-column entry is multiplied by 3/2. Hence the path is uniquely no-swap, the last pivot is c_n=(3/2)^(n-1), the input max is 1, and the growth is exactly c_n. All active entries are at most 2^n in magnitude.
- **All-n box radius (lines 94–126):** With B=2^(n+2) and delta=2^(-(n^2+n+1)), the exponent identity (n+2)(n-1)-(n^2+n+1)=-3 gives B^(n-1)delta=1/8 exactly. Thus the claimed induction envelope never exceeds 1/8. Before each update, the actual pivot is at least 7/8 while every competitor is at most 5/8. There is no circular assumption of a no-swap path: the error bound proves that the actual PP algorithm selects it at each step.
- **Multiplier/update bound (lines 128–159):** Writing the perturbed pivot as 1+d and competitor as -1/2+f with |d|,|f|<=e yields q-b=(f+d/2)/(1+d). Therefore |q-b|<=3e/(2(1-e))<=2e. Also |q|<=5/7. Subtracting the rank-one updates gives exactly the displayed three-term difference. Its max is bounded by (1+5/7)e+2e*2^n <=(2+2^(n+1))e <=Be. This completes the induction in every n, for every point of the closed box.
- **Nonsingularity and strict growth (lines 162–172):** The final scalar is at least c_n-1/8>0; together with positive earlier pivots this proves every box matrix is nonsingular. Input max is at most 1+delta<=9/8. Consequently growth is at least (8c_n-1)/9 >=7c_n/9>c_n/2. The final scalar is an active Schur-complement entry, so this is valid for the full growth definition; no upper bound on other perturbed entries is needed here.
- **Probability (lines 178–209):** For C=I_n (also C=0), each required Gaussian coordinate lies in an interval of length 2delta centered in [-1,1]. Those intervals lie in [-2,2]. The standard-normal density is at least exp(-2)/sqrt(2pi)>1/32; the manuscript's elementary e<3 and pi<4 justification is valid. Independence gives P(E_n)>=(delta/16)^(n^2)=2^(-K_n), K_n=n^2(n^2+n+5). The inequality K_n<=3n^4 holds for n>=2. This is a full-dimensional Gaussian event, not a measure-zero or tie-dependent event.
- **Every proposed constant pair (lines 215–246):** For fixed arbitrary positive real c1,c2, set x_n=c_n/(2n^c1). Then x_n/K_n tends to infinity, as the displayed logarithm verifies. Thus eventually x_n>=1 and c2*x_n>K_n, and the exact event threshold x_n*n^c1 equals c_n/2. Hence the proved probability lower bound is strictly larger than 2^(-c2*x_n). This defeats every universal pair, not just the illustrative numerical examples. The unrestricted x range is essential and explicitly acknowledged.

## Verification evidence

`pr130-independent-check.py` is newly written stdlib-only code; it imports no submitted checker. Exact Fraction calculations verify the unperturbed elimination in n=2,...,12, 132 independently chosen endpoint/interior perturbations, scalar inequalities for n=2,...,256, and four illustrative contradiction dimensions including c1=50,c2=1/100 at n=924. `pr130-independent-check.json` records the results. These finite checks corroborate the analytic all-n proof; they do not establish its universal quantifiers by themselves.

Before execution, I read the full submitted `originals/verify_bounds.py` and the separate submitted exact-check source. The interval checker uses outward-rounded integer dyadic intervals, checks strict pivot bounds, and writes only the explicitly supplied certificate path. Its default full-box runs n=2,...,16 and scalar checks n=2,...,256 pass. Output and certificate are saved as `pr130-submitted-interval.txt` and `pr130-submitted-interval.json`. No repository files were changed; checkout status remained clean.

## Primary source

I fetched the primary author PDF directly and visually inspected its complete printed page 52 (the text extraction has unusable font encoding). Section P6 contains Conjecture 16, “Exponential Stability of GEPP,” with the same displayed tail threshold x(n/sigma)^c1 and upper bound 2^(-c2*x), for norm-bounded deterministic centers and sigma-Gaussian perturbations. The source is correctly attributed to Spielman and Teng; the solution explicitly distinguishes the canonical fully quantified target from historical motivation. The source paragraph does not itself spell out the x range, but the preserved canonical question does, so the counterexample's scope is accurately stated.

Primary source: https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf
Publication DOI: https://doi.org/10.1017/CBO9780511721571.010
Local source copy: `/private/tmp/nla-review-trace/pr130-Spielman-Teng.pdf`.
