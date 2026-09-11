# IE-18 independent proof review

Date: 2026-09-11. **PASS — the full canonical finite four-step identity is false, even for positive-definite contractions with positive-definite complements.** Recommend **Resolved (counterexample)** for IE-18. The separate asymptotic worst-case convergence assertion remains outside this result. No mathematical proof correction is required.

## Complete source and target match

Read all of the recovered standalone `proofs/IE-18.tex`, including both examples, every asymptotic expansion, recurrence check, and scope statement. Complete UTF-8 source with CRLF replaced by LF and no trimming: **5967 bytes**, SHA256 **`482c14b1ea7072d4d546c181eda4aa131bc70fcdf51710485ea501e869638beb`**. Its preamble is included and it has no omitted external TeX input.

The provisional label matches `linear-systems-and-elimination/IE-18/README.md`. The maps agree exactly: A=I-M, alpha(v)=v^T Av/||Av||², and R(v)=M(I-alpha(v)A)v. The canonical asks for the maximum norm amplification of R composed with itself, with the squared pairwise expression on the right. It does not ask for a squared-norm ratio or for an asymptotic rate. The manuscript correctly compares a squared-norm ratio with Lambda(M)².

Locators: Section 1, line 30, defines the finite claim; Section 2, line 40, gives both exact examples; Section 3, line 62, proves unbounded underestimation; Section 4, line 89, checks the raw recurrence; Section 5, line 95, records source/scope. The manuscript contains no numbered theorem environments.

## Exact counterexamples — PASS

For M=diag(1/10,1/2,3/5), all eigenvalues lie strictly between zero and one, so M and A are positive definite and satisfy every canonical assumption. With v=(1,1,1), direct substitution gives alpha=90/61, first residual (-2,8,15)/61, and second alpha=3140/1381. The second residual is (289,-756,1125)/84241. Its squared norm divided by three is 1920682/21289638243.

Evaluating all three distinct eigenvalue pairs gives maximum Lambda=1/121. Therefore the claimed equality is contradicted by a single actual residual direction: its squared ratio exceeds 1/14641 because 1920682 times 14641 equals 28120705162, greater than 21289638243. No maximizer search is necessary: one value strictly larger than the proposed maximum suffices. The residual and its first image are nonzero, so no termination convention or zero denominator is used.

The second example M=diag(0,1/2,2/3) also satisfies the canonical assumptions, despite being singular as an iteration matrix; A is still invertible. It gives alpha=66/49, first residual (0,8,18)/49, second alpha=35/13, and second residual (0,-18,16)/637. All three pair denominators are positive, including the pairs with the zero eigenvalue. The maximum pairwise value is 4/289. The stated squared comparison and integer cross multiplication are correct.

The one-cycle raw recurrence also matches the map. Here d=Mr-r=-Ar and gamma=-(Mr)^T d/||d||². Consequently `1+gamma=(r^T A r)/||Ar||²=alpha(r)` for symmetric A. Thus `r1+gamma d=r-alpha(r)Ar`, and applying M yields R(r). Running two cycles therefore gives the same four-original-step map. This excludes confusion with windowed Anderson acceleration, ordinary GMRES(1), or a different restart convention.

## One-parameter family — PASS

For 0<epsilon<1/2, all diagonal entries of M_epsilon=diag(epsilon²,1/2,1/2+epsilon) lie in (0,1), so both M_epsilon and I-M_epsilon are positive definite. At epsilon=0 the first residual is (0,1/6,1/6), and the first and second alpha denominators stay nonzero. Hence the rational expressions admit Taylor expansions on a neighborhood of zero; the expansion does not rely on division by a vanishing second residual.

Independent differentiation confirms alpha(0)=4/3 and alpha'(0)=2/9. The first residual derivative is (0,-1/18,17/18). In the second alpha quotient, the numerator has value 1/36 and derivative 13/108, while the denominator has value 1/72 and derivative 5/108. The quotient rule gives beta(0)=2 and beta'(0)=2. The second residual vanishes at zero and has derivative (0,-1/12,1/12). Its norm divided by ||v||=sqrt(3) is therefore epsilon/(6sqrt(6))+O(epsilon²) for positive epsilon.

The pair involving 1/2 and 1/2+epsilon has positive denominator 1/2-epsilon² and contributes `[epsilon(1+2epsilon)/(2-4epsilon²)]²=epsilon²/4+O(epsilon³)`. Each pair involving epsilon² has numerator O(epsilon²) and denominator tending to 1/4, so its squared contribution is O(epsilon^4). Thus the displayed nonzero pair is maximal for all sufficiently small positive epsilon. Dividing the two expansions gives `2/(3sqrt(6)) epsilon^(-1)+O(1)`, diverging to infinity.

The conclusion that no fixed multiplicative constant repairs this uniform finite-step upper bound is valid: the maximum over v is at least the ratio for the fixed v used here. This does not say that the amplification itself diverges; it tends to zero more slowly than the proposed bound. Nor does it imply that the same underestimation persists along an asymptotic orbit.

## Arithmetic checks and full scope

The relevant `aa`, `aa_pairs`, `aa_raw`, and `ie18` functions in `verification/checks.py` and the arithmetic operations in `exact.py` were inspected. They use exact Fraction arithmetic and correctly compare the squared ratio to the square of the pairwise bound. The finite epsilon checks support examples only; they are not the proof of the asymptotic expansion, which was checked analytically above.

The reviewer-created `verification/reviewer_ie17_19.py` independently recomputes both composed maps and all pair values without importing submitted code. Its exact output, saved in `reviewer_ie17_19.json`, agrees with both displayed examples and passes the strict inequalities. The parent task reruns the supplied verifier separately.

The manuscript's general definition only explicitly defines Lambda for nonzero pair denominators. This causes no gap for its universal counterexamples or family: all the used denominators are nonzero. The canonical convention that a pair of zero eigenvalues contributes zero does not alter any calculation. Arbitrary symmetric matrices with other repeated eigenvalues need not be classified to refute a universal identity.

## Primary-source mapping

The [primary arXiv v4, equations (9), (16), (24), and Conjecture 10/(27)](https://arxiv.org/html/2312.04776v4) confirms the mapping. Equation (16) explicitly states X(v)v=R(R(v)); Lemma 8/(24) evaluates the pairwise maximum as exactly the squared expression used here. Conjecture 10 is therefore directly contradicted. The neighboring Theorem 9 gives an asymptotic lower bound and a dimension-two equality, which are not refuted by these examples. A failed finite-step sufficient route does not logically negate its hoped-for asymptotic conclusion.

**Final scope: PASS for the entire recovered IE-18 manuscript and a complete negative answer to the current canonical finite-step identity. Retain the distinction from asymptotic convergence and from other Anderson variants in any status update.** This audit does not establish publication priority.
