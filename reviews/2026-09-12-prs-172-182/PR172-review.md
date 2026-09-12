# Independent mathematical and statement-fidelity review — PR #172

**Verdict: PASS, with no mathematical or statement-fidelity blocker found.**

Reviewer: OpenAI Codex AI agent `/root/audit_functions_randomized`, independently reading the actual proof rather than adopting submitted PASS reports. Reviewed head: `185a7c394b3c89a28cc0daaab12cc54de6c04173`, in `/private/tmp/nla-audit-172`. Date: 2026-09-12. This is an AI mathematical/source review, not human peer review. I did not run Lean locally or authenticate upstream CI; the integrating agent separately owns that operational gate.

## Scope and source correspondence

I read the complete actual `Definitions.lean`, `Algebra.lean`, `Roots.lean`, `Sums.lean`, `Proof.lean`, `Challenge.lean`, and `Solution.lean`; the canonical README, numerical targets, source map, formalization manifest, Comparator and package/dependency configuration; the complete Colbrook manuscript; and the current contribution and Lean review policies. Ordinary Git comparison confirms that the original canonical statement is unchanged from base `f41f1f9ffa2171550d4bb795862c6170c4f26070`. The actual definitions/proof/challenge/exports and package configuration are also unchanged from the README's immutable proof revision `bf144a8ea84992d64f79f4425b18352843376286`.

The primary original source is [Dereziński, Khanna and Mahoney, §5, Conjecture 1](https://arxiv.org/html/2002.09073). It asks for convexity of the elementary-symmetric ratio on the integer set `[n]` for every strictly positive tuple. The canonical formulation as nonnegative second differences at `2≤j≤n−1` is faithful. Its expectation identity and sampling consequences motivate the question; they are not additional premises or conclusions of this scalar target.

In `randomized-and-low-rank-approximation/RA-07/lean/NLA/RA07/Definitions.lean:22–54`, `elementarySymmetric` is the actual sum of products over all subsets of the required size, not a coefficient or expectation defined to satisfy the theorem. `errorSequence` is ordinary real division of these sums with the actual factor `j+1`. `generatingPolynomial` and `iteratedGeneratingDerivative` are actual polynomial products and differentiation. `ConvexityConjecture` retains every `n≥3`, every strictly positive real tuple, and every original index. There is no normalization, sorting, distinctness, numerical cutoff, prescribed root list, or assumed factorization. Natural subtraction cannot truncate any relevant index under these hypotheses.

The README's exclusions at line 46 are accurate: the manuscript additionally proves strict monotonicity, the second difference at index one, and determinantal-sampling and stable-rank corollaries. These are outside the six advertised Lean exports. That does not weaken the retained canonical target.

## Proof audit

**Actual sums and derivatives.** `Algebra.lean:27–61` proves the empty and oversized subset conventions, positivity of every admissible elementary sum, the generating-polynomial coefficient identity, and `P^(j)(0)=j! e_j`. Positivity uses a nonempty family of positive products, including `j=0`. Thus `e_n>0`, `e_(n+1)=0`, and the final sequence value zero are consequences of the actual definitions. `Proof.lean:23–46` derives the derivative-ratio and derivative-shift bridges; nonzero factorial and scaling factors are proved before cancellation. The ratio identity is valid even with zero numerators. The proof does not cancel an unproved nonzero elementary sum.

**Factorization is proved unconditionally.** `Roots.lean:23–51` proves the exact degree `n-d` and positive value at zero for every `d≤n`. `Roots.lean:54–105` puts the original complex roots on the strictly negative real ray and applies Gauss–Lucas inductively. I retrieved and read the actual [pinned Mathlib Gauss–Lucas source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean), including its proved theorem and hypotheses. It gives containment in the ordinary convex hull of the original complex roots under positive polynomial degree, with no distinct-root premise. The negative real ray is convex, and the implementation supplies positive degree before each differentiation. It therefore proves strict negativity, without incorrectly taking the closure of that ray.

`Roots.lean:107–185` descends complex roots to the real field and uses actual splitting and the complete root multiset. The factor count equals the natural degree; the list conversion retains repeated roots. Each reciprocal parameter is `-1/r>0`, and each factor `X-r` is correctly rewritten as `(-r)*(1+(-1/r)*X)`. Evaluating the reconstructed polynomial at zero proves the scale to be the actual derivative's value, rather than assuming that normalization. At `d=n`, the derivative is a positive constant and the factor list is empty; the induction does not apply a positive-degree theorem to that constant. No root-set argument is incorrectly used as a substitute for multiplicity counting.

**The scalar certificate.** `Sums.lean:19–48` proves the first three actual product derivatives at zero by finite-set induction. `Sums.lean:50–131` splits ordered off-diagonal pairs into two symmetric halves and proves

```
s1*s3 - s2^2 = sum_(a<b) μa*μb*(μa-μb)^2,
s1^2 - s2 = 2*sum_(a<b) μa*μb.
```

Each unordered pair is counted exactly once. `Sums.lean:133–161` establishes strict denominator positivity for every positive tuple with at least two entries, using the actual pair of indices 0 and 1; it separately proves the gap nonnegative. Equal parameters are permitted and can give gap zero.

I independently rederived the fraction identity: setting `a=s1`, `b=s2`, and `c=s3`, the second difference is

```
a - 2*(a^2-b)/a + (a^3-3*a*b+2*c)/(a^2-b)
  = 2*(a*c-b^2)/(a*(a^2-b)).
```

The required two factors in the denominator are proved nonzero before `field_simp` in `Proof.lean:49–65`. For the original index, `Proof.lean:67–96` chooses the actual derivative of order `j-1`, proves its factor count `n-(j-1)≥2`, obtains its factorization as a conclusion, and transfers all three original ratios to this scalar identity. The final theorem then uses the nonnegative gap and positive denominator. The bridge is not a conditional certificate masquerading as the target.

**Endpoints and nonvacuity.** At `j=n−1`, the factored derivative has degree two, its third derivative is zero, and the denominator remains positive. The smallest case `n=3,j=2` is included. For the concrete positive tuple `(1,2,3)`, the original values are `F1=11/3`, `F2=18/11`, `F3=0`, giving second difference `13/33`. The normalized derivative has reciprocal-root sum `11/3` and product `3`, hence gap `13/3` and denominator `22`; the certificate also gives `13/33`. This calculation independently checks the nontrivial endpoint and factor-of-two normalization. If all original entries equal a positive `λ`, then `Fj=(n-j)λ` and every second difference is zero, consistent with the asserted weak inequality and repeated-root treatment.

## Exports, trust and remaining limits

All six public `Solution.lean` declarations reproduce the six Challenge signatures and directly use the actual proved results. Comparator selects all six, has no definition holes, and permits only `propext`, `Classical.choice`, and `Quot.sound`. Source inspection found no `sorry`, `admit`, custom axiom, native-decision proof, unsafe evaluator, or custom elaborator in the actual proof chain. The six deliberate Challenge placeholders are separate and are not imported by the proof or Solution. Proof files use standard Mathlib algebra, finite-sum, polynomial and complex-root APIs; LeanCert provides explicit kernel trust assertions rather than an artificial numerical certificate.

The declared toolchain is Lean 4.33.1, with LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The default package build target is the statement-only Challenge, so a default build alone would not suffice; the separate Comparator/Solution replay gate is essential. I have not inferred that gate from metadata or submitted reviews. The proof-bearing mathematical/source inspection supports the **complete affirmative answer to the retained RA-07 scalar target**. Promotion to “Lean verified” is appropriate once the integrating agent's independent live-CI, statement-comparison, permitted-axiom and default-kernel checks succeed.
