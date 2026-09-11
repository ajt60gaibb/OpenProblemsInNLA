# IS-04 independent review: explicit odd prime-square family

Review date: 2026-09-11. The complete submitted Markdown manuscript and generated LaTeX source, the current canonical IS-04 README, `verification/odd_family.py`, and the sign-family portion of `verification/check_round3.py` were read. The external character-sum input and the precise related source question were checked against the cited primary papers. This review is independent of the integration agent's supplied-code reproduction.

## Verdict and exact scope

**PASS for the complete submitted mathematical result. Partial progress only for canonical IS-04; retain its Partially resolved status.**

For every odd prime `p>=13`, the construction gives a deterministic real sign matrix of order `p^2` whose singular values lie between `p-2-3sqrt(p)` and `p+2+3sqrt(p)`. Its condition number is at most their ratio and tends to one as `p` tends to infinity. For every prime `p>=361` it is at most `210/151<sqrt(2)`. Thus the manuscript does answer the distinct **Problem 13** of Alexeev–Jasper–Mixon affirmatively: an explicit infinite family of odd-order approximate Hadamard matrices with condition numbers below `sqrt(2)`.

The canonical target is `sup_n h(n)=2`, equivalently a condition-number-at-most-two example for **every** order. This proof gives no all-order construction, no reduction of every remaining order to a prime square, and no completion of that supremum. The bound for `13<=p<361` is the displayed ratio, not a blanket claim that the ratio is below two throughout that range. No required correction to the source was found. This review does not assert priority or formal verification.

## Full source identity

Source directory: `.cache/colbrook-round3/nla_round3_submission/manuscripts/`.

| Complete source | Normalized bytes | SHA-256 of full UTF-8/LF content |
| --- | ---: | --- |
| `IS-04-explicit-odd-family-partial.tex` | 12,992 | `94e3825ea8f0d6b1ee4a067d5f59da95e67b8b6a94e7578ddd237bb415af771c` |
| `IS-04-explicit-odd-family-partial.md` | 10,233 | `c808b4efee6c02fee78832755af7234679f8aec3cbae1b6baa8c6603bded2606` |

Each hash was computed by decoding the entire file as UTF-8, replacing CRLF with LF, and re-encoding without trimming, deleting front matter, or removing terminal newlines. The LaTeX preamble is included; it introduces no additional mathematical hypothesis. The two versions contain the same theorem, construction, proof, scope statements, and source references. No manuscript or canonical file was edited by this reviewer.

Canonical source compared: `eigenvalues-and-inverse-problems/IS-04/README.md`, marked Partially resolved and last checked 2026-09-10 at the start of this review. Its real sign entries, Euclidean spectral condition number, singular-input convention, unrestricted order, and lack of symmetry/circulant constraints were explicitly checked.

## Complete proof audit

### Section 2: sign-valued kernel and deterministic construction, equations (3)–(6)

**PASS.** Since `d` is a nonzero nonsquare and `p` is odd, `x^2-dy^2=0` forces `(x,y)=(0,0)`: if `y` is nonzero it would make `d` a square, and if `y=0` it forces `x=0`. Thus the unmodified kernel is a sign at every nonzero group element.

The first coordinate of `Gamma(t)=(2dt,1+dt^2)` makes the map injective because `2d` is invertible. If its first coordinate vanishes then `t=0`, at which its second coordinate is one, so the origin is excluded. Direct expansion gives

`Q(Gamma(t))=4d^2t^2-d(1+dt^2)^2=-d(1-dt^2)^2`.

The factor `1-dt^2` is nonzero for every `t`, including zero, because `d` is nonsquare. Therefore the quadratic character on the entire parabola is `chi(-d)=-epsilon`. Flipping exactly the nonzero quadratic-residue parameter values changes `-epsilon` to `epsilon`, while filling the origin changes zero to `epsilon`. The two modifications have disjoint supports. Every resulting kernel entry is exactly `-1` or `1`, and its flip set has exactly `(p-1)/2` elements.

Choosing the least positive nonsquare is a deterministic finite procedure and supplies a concrete construction for each prime. Indexing by the additive group `F_p^2` produces an order-`p^2` real sign matrix. It does not require identifying that group with a cyclic group, which is impossible here, and no such identification is used.

### Section 3: Lemma 2, equation (7)

**PASS.** The quadratic Gauss sum is nonzero, with `tau^2=epsilon*p`. The expansion of `chi(s)` holds also at `s=0`, because the sum of the nontrivial multiplicative character is zero. For nonzero `s`, changing variables in the additive sum gives the usual factor `chi(s)`; the quadratic character is its own inverse.

For each nonzero `r`, completing the two squares produces the phase

`exp(2*pi*i*(-u^2+d^(-1)v^2)/(4r*p))`.

The product of the two quadratic character factors is `chi(r)*chi(-dr)=chi(-d)=-epsilon`; multiplying by `tau^2=epsilon*p` gives exactly `-p`. This verifies the displayed sign and normalization in the product formula. There is no lost `p` or square-root factor.

Putting `R=u^2-d^(-1)v^2`, the remaining sum is `-(p/tau)*sum_(r!=0) chi(r)e_p(-R/(4r))`. At zero frequency it vanishes. For every other frequency, anisotropy of the dual form implies `R!=0` because `d^(-1)` is nonsquare as well. Inverting `r` leaves `chi(r)` unchanged and reduces the expression to a one-dimensional Gauss sum. Since four is a square, the result is `-p*chi(-R/4)=-epsilon*p*chi(R)`. Hence every nonzero coefficient has modulus exactly `p`, while the trivial coefficient is exactly zero.

This verifies the full Fourier identity, rather than only its absolute-value consequence. It works for both residue classes of odd primes modulo four.

### Section 4: mixed Weil estimate, equation (8)

**PASS, with the external input correctly isolated.** For `(alpha,beta)!=(0,0)`, the polynomial `f(t)=alpha*t+beta*t^2` has degree `m=1` or `2`, strictly less than the odd characteristic `p`. On `U=P^1-{0,infinity}=G_m`, the rank-one tensor `Kummer(chi(t))` times `Artin–Schreier(e_p(f(t)))` is lisse and pure of weight zero. At zero the additive factor is unramified and the quadratic multiplicative factor has nontrivial tame monodromy, so the tensor is geometrically nontrivial. Its only wild contribution is at infinity, of Swan conductor `m`: the pole degree is below `p`, so no Artin–Schreier degree reduction is possible.

For this rank-one sheaf, compactly supported degree-zero cohomology vanishes on the affine curve, and degree-two cohomology vanishes because the geometric representation has no trivial coinvariants. Since `chi_c(G_m)=0`, the Euler–Poincaré formula yields `dim H_c^1=m`. The trace formula and the weight bound then give absolute trace at most `m*sqrt(p)<=2sqrt(p)`. Removing zero from the domain is consistent with `chi(0)=0`; no endpoint term is omitted. In the linear case the stronger `sqrt(p)` estimate is available but is not needed.

Primary-source verification: Proposition 10.1 constructs the mixed character sheaf and records its weight and ramification. Its hypotheses apply with `phi_2(t)=t`, which is not a constant times a square, including when `phi_1` is linear. Equation (8.8) is the Euler–Poincaré identity. Equation (9.4) and the following argument supply the trace formula and the `sqrt(p)` weight estimate. These support the claimed specialization and constant, not merely an unspecified big-O estimate. [Fouvry, Kowalski, and Michel, *Algebraic twists of modular forms and Hecke orbits*, Sections 8–10](https://arxiv.org/html/1207.0617v5).

### Section 5: flip transform and trivial frequency, equations (9)–(11)

**PASS.** The expression `(1+chi(t)-1_(t=0))/2` is exactly the indicator of the nonzero squares, including its zero value at `t=0`. Substitution of `Gamma(t)` separates off the constant factor `e_p(v)` and leaves the polynomial `2du*t+dv*t^2`, giving equation (9) with the correct minus-one term.

At a nonzero frequency, that polynomial is nonconstant: if `v!=0` its quadratic coefficient is nonzero; if `v=0`, then `u!=0` and its linear coefficient is nonzero. The untwisted sum has modulus `sqrt(p)` in the former case and is zero in the latter. The mixed bound therefore gives `|2*widehat(1_S)|<=3sqrt(p)+1`. Adding the filled-origin contribution, of magnitude one, yields `|widehat(a)-widehat(c)|<=2+3sqrt(p)`.

The zero frequency is treated separately and exactly. The base sum is zero and the modifications sum to `epsilon+2epsilon*(p-1)/2=epsilon*p`. Thus the formerly zero eigenvalue is moved to modulus `p`. This exact correction is essential: applying only a perturbation estimate at zero would not prove invertibility or good conditioning.

### Theorem 1: singular values and constants

**PASS.** Translation convolution on a finite abelian group is diagonal in the normalized character basis. With the manuscript's positive-exponent transform, the eigenvalue may be indexed by the negative frequency depending on the character vector convention, but this permutes the same list. The diagonalizing matrix is unitary, so the matrix is normal even when it is not symmetric. Its singular values are therefore exactly the absolute Fourier coefficients. Real entries do not require its eigenvalues to be real, and the proof makes no such assumption for the modified kernel.

At all nontrivial frequencies, the reverse triangle inequality supplies the lower bound `p-2-3sqrt(p)` and the triangle inequality supplies the upper bound `p+2+3sqrt(p)`. The trivial frequency has modulus exactly `p`, so it also lies in this interval. Positivity of the lower endpoint at `p=13` follows from `11^2>9*13`; the function is increasing thereafter because its derivative is `1-3/(2sqrt(p))>0`. This establishes nonsingularity for every stated prime and justifies dividing the singular-value bounds.

Writing `r_p=2/p+3/sqrt(p)`, the ratio is `(1+r_p)/(1-r_p)` and differs from one by `2r_p/(1-r_p)=O(p^-1/2)`. The lower bound `kappa>=1` gives the stated convergence. Since the order is `n=p^2`, this is `1+O(n^-1/4)` along the constructed sequence, with no extension to unconstructed orders.

For `p>=361`, `r_p<=2/361+3/19=59/361`; the condition ratio is at most `420/302=210/151`. The exact squared comparison `210^2=44100<45602=2*151^2` proves the strict `sqrt(2)` threshold. The threshold 361 need not itself be prime; the assertion quantifies over primes above it (the first is 367). Infinitely many such primes exist, supplying infinitely many distinct odd orders.

## Source-question alignment

Alexeev–Jasper–Mixon's Section 6, Problem 12 is the all-order supremum question. Problem 13 separately requests an explicit infinite odd-order family below `sqrt(2)` and imposes no symmetry or cyclic-circulant restriction. The manuscript meets Problem 13 exactly. The same section states that the previously proved convergence `h(n)->1` reduces Problem 12 to finitely many remaining dimensions; the prime-square construction does not complete those remaining cases. [Alexeev, Jasper, and Mixon, *Asymptotically optimal approximate Hadamard matrices*, Section 6](https://arxiv.org/html/2511.14653v1).

The proof does not establish the optimal all-order decay exponent of the separate canonical IS-05. A rate along an infinite subsequence is not an all-order rate.

## Code and reproducibility audit

`verification/odd_family.py` was read in full. It uses deterministic trial-division primality checking, finds a nonsquare from the exact quadratic-character table, constructs the base and modified kernels with integer arithmetic, and indexes the dense matrix by group differences. The default memory guard keeps the supported calculations within small fixed-width integer ranges; the mathematical construction itself is not limited by that implementation budget. The optional dense constructor enforces an order guard. Spectral summaries use a two-dimensional FFT and are explicitly labelled floating-point diagnostics.

The full `sign_family_checks` routine in `verification/check_round3.py` was inspected. It checks 18 primes from 3 through 1009. Exact integer comparisons verify the sign property, parabola identity, flip count, and zero-frequency sum. It numerically compares the base FFT with equation (7), checks all nontrivial mixed-sum frequencies via the parabola kernel, and checks both singular-value inequalities. At `p=3,5,7,11`, it additionally compares the FFT singular-value list with a dense SVD. The small primes below 13 test algebraic identities and numerical examples; they are not asserted to satisfy the theorem's positive lower bound.

The mixed-kernel FFT includes a phase factor and an invertible reparameterization of the linear/quadratic coefficients, so its complete frequency grid does test every nontrivial coefficient pair for each sampled prime. Overwriting the trivial mixed coefficient with zero matches the exact sum of the quadratic character, which vanishes. The FFT uses the opposite exponent sign from the manuscript, but the base quadratic form is even and the other claims are magnitude bounds, so this convention does not invalidate the checks.

These finite numerical samples cannot certify the uniform character-sum theorem. The exact proof and verified external input establish the infinite-family statement. The integration agent's fresh reproduction records should be cited separately for the actual run results; this report does not treat supplied success labels as independent proof.

## Remaining target and changes

- **Canonical status:** retain Partially resolved.
- **Verified result:** the explicit prime-square construction and its complete bounds; affirmative answer to related source Problem 13.
- **Remaining canonical task:** prove the at-most-two condition bound for every order still untreated by existing all-order asymptotic results, or exhibit an order with `h(n)>2`.
- **Required mathematical/source changes:** none found.
- **Priority and formal certification:** not established by this review.
