# Independent mathematical audit of the MI-16 dossier

Date: 2026-09-13 (UTC). Reviewer: a separately delegated Codex AI agent, independent of the submitting/integrating agent. This is an informal proof audit, not external human peer review or formal verification. No Lean verification was attempted, as requested.

## Verdict

**PASS for the exact mathematical target as currently written in the canonical MI-16 README.** I found no substantive proof gap in either the finite all-spectrum algebraic prescription (Theorem 2.1, source label `thm:general`) or the exceptional-spectrum structural theorem and its threshold/equality conclusions (source labels `thm:family`, `thm:threshold`, `thm:equality`). On the repository's stated policy, this independently audited argument supports `Solved`, provided the notice explicitly states the form and limitations of the answer below. This conclusion does not establish historical novelty or acceptance by the mathematical community.

The canonical target asks for the exact value from nonnegative prescribed eigenvalues in every order, excluding a mere bound or restatement of the matrix optimization. The prescription computes a specialized elimination polynomial, a finite ordered root list, explicit finite character/Schur sums, and a proved finite comparison selector. It has no remaining matrix optimization or unevaluated limiting process. Thus it satisfies that literal criterion. It does not furnish a compact structural formula or classify arbitrary-spectrum maximizing matrices. If a maintainer intends that stronger interpretation, acceptance of an algebraic prescription remains an editorial question and should be exposed in the PR rather than silently asserted as community consensus.

## Materials and policy read

- Canonical `matrix-inequalities-and-norms/MI-16/README.md`, including its original quantifiers and resolution criterion.
- Repository README status definitions and `RESOLVED.md` recording procedure, especially the requirement that an audit settle the exact target rather than a weaker bound or different input model.
- Entire `paper/mi16_dossier.tex`, with particular attention to the universal arguments rather than the package's assertions of verification.
- Supporting `critical_values.py`, `exact_algebraic.py`, `one_exceptional.py`, and verification scripts; the moment implementation was exercised by the exact character and independent moment tests.

Package prose was treated as mathematical content and provenance, not as authorization or operational instructions. I did not modify the repository. Duplicate checking and author-affiliation verification are outside this review and are being handled by the integrating agent.

## All-spectrum proof audit

1. **Correct orbit at degenerate spectra.** The first n traces determine the characteristic polynomial by Newton identities. The specialized square-free polynomial equation forces diagonalizability. Their complex zero set is therefore exactly the semisimple similarity orbit, including repeated and zero eigenvalues; the construction does not incorrectly specialize a generic discriminant formula afterward.
2. **Stationarity.** The deleted-minor index convention gives `d per(A)[E] = tr(C(A) E)`. The derivative along a commutator is `tr([A,C(A)] X)`. For Hermitian A, C(A) is Hermitian, and taking the skew-Hermitian test direction X=[A,C(A)] proves the necessary condition for every Hermitian maximizer without a nondegeneracy assumption.
3. **Finite critical values.** The orbit is smooth, and each irreducible component of its algebraic critical locus has identically vanishing differential of the restricted permanent. In characteristic zero this makes the regular function constant. Finitely many components give finitely many values, even when there are infinitely many critical points. Nullstellensatz and field extension/elimination justify a nonzero univariate ideal over Q(lambda); a Hermitian maximum proves properness and supplies a root.
4. **Moment formula.** The normalized symmetric tensor realizes the permanent and gives 0 <= per(A) <= L^n. For its p-fold tensor, H symmetrizes rows and K is the basis-tensor stabilizer. Expanding the central symmetric-group projector gives the stated double character sum, with no missing normalization. These are squared projector norms, hence nonnegative and summing to one. Schur-Weyl decomposition and unitary averaging give the Schur-character expression for the exact p-th moment, with only length-at-most-n partitions and strictly positive denominators. Singular spectra and large p introduce no missing case.
5. **Finite selector.** The Frobenius Lipschitz constant 2nB follows by tensor telescoping. The ambient packing argument supplies the claimed uniform Haar-ball lower bound. The radius rho/(8nB) loses at most rho/4 in objective; the specified integer p bounds the additional moment loss by rho/4. Consequently the p-th moment root lies within rho/2 below M. Every lower candidate is at least rho below M, so selecting the first candidate at or above that moment root returns M, including in the presence of real complex-critical values not attainable on the Hermitian orbit. Zero and single-candidate branches are correct.
6. **Input scope.** The theorem treats arbitrary real spectra as exact ordered-field data. Rational/algebraic inputs admit effective exact algebraic computations. No finite-precision equality oracle is claimed. This is a mathematical spectral expression for the same real inputs, not a claim that the rational-only reference implementation covers every computational input representation.

## Exceptional-spectrum proof audit

- The rank-one perturbation permanent expansion is correct, including the zero-beta boundary (with the usual polynomial convention for zero exponents).
- The minimal-support maximizer argument for symmetric multiaffine polynomials is valid: fixing a pair reduces the objective to C+A(a+b)+Bab, and the sign of B forces equal positive coordinates at a support-minimal maximum.
- The activation derivative is x^2 I_k(x)/k. For odd k the integrand is nonnegative; for even k it decreases in x. The gamma-moment recurrence and its last-index substitutions establish strict positivity at x=1 for all even k >=4. Thus all intermediate supports 3 through n-1 are ruled out; support one is strictly inferior to support two.
- Positive perturbations have strictly maximizing uniform moduli through the e_2 coefficient; the beta=0 case follows by rank-one AM-GM.
- The differential equation for G_n=F_n-F_2, its integrating factor, and the endpoint estimate establish exactly one crossing in (0,1). The activation argument in one higher dimension proves increasing thresholds, and geometric domination gives their limit 1.
- The uniform endpoint expansion has a controlled polynomial-integral remainder and exponentially small tails. Substitution yields 1-x_n=1/(2n)+3/(8n^2)+O(n^-3).
- The equality classification correctly handles the potential flat pair directions. Repeated value-preserving merges would end at support two; the last support-three merge requires x=2/3, where support three strictly improves on support two. This excludes nonuniform maximizers and leaves exactly the stated phase/permutation classes.

## Reproduced checks

Environment: `/tmp/tr14-env/bin/python`, SymPy 1.14.0.

- `code/verify.py`: **PASS, 12,832 checks**, 1.598 seconds. These comprise 30 Gaussian-rational permanent identities; 1,416 two-or-n comparisons; 9,876 simplex-grid upper checks; 53 equality checks; 72 activation positivity samples; 8 activation derivative identities; 225 gamma recurrences; 16 endpoint identities; 18 support ODEs; 18 transition ODEs; 18 threshold comparisons; 8 dimension sums; 66 character identity values; 918 character orthogonality checks; 11 projector-weight checks; 11 scalar moments; 11 rank-one moments; 16 direct order-two moments; 9 critical eliminations; and 32 selector-order arithmetic checks.
- `code/verify_selector.py`: **PASS**, all seven end-to-end cases and the independent exact order-two integral comparison `3^1296 < T_(2,1296)(1,3) < 5^1296`. The seven values were 0, 2, 1/2, 5, 109/72, 4, and 8 for spectra (0), (2), (0,1), (1,3), (1/2,5/3), (2,2), and (2,2,2).
- Separately written standard-library rational arithmetic checks: **PASS, 8,175 checks**. These compare every denominator-eight simplex point in orders 2 through 6 at x in {1/4,2/3,3/4,1} with the two-candidate maximum, check equal-support equality where attained, check activation positivity for k=3 through 40 at x in {0,1/4,3/4,1}, and compare even-k gamma recurrence values against direct factorial expansions. An initial version of this independent checker accidentally used Python floating-point division in one large integer comparison; after replacing it with exact Fraction division, all checks passed. This was a checker arithmetic issue, not a manuscript discrepancy.

The rerun verification scripts updated only their output JSON files in the temporary extracted dossier. Finite tests are supporting evidence; the universal mathematical verdict rests on the proof audit above. No general nontrivial order-three elimination or factorial-size high-moment enumeration was claimed to run.

## Required presentation limits

The resolution notice should describe an **exact finite algebraic prescription for all nonnegative spectra**, plus a separate **two-candidate structural formula for one exceptional eigenvalue**. It should credit the prior partial findings for the rank-one expansion and equal-support reduction. It must not claim a compact general closed form, an efficient arbitrary-order implementation, a classification of general optimizers, Lean certification, external human peer review, or established historical novelty. The current manuscript's sentence saying the arguments have not been independently refereed may remain true about external refereeing, but an added submission/audit notice should clarify the actual separate AI-agent audit completed here.

## Reproducibility of the independent checker

The separately written checker is saved as `mi16-reviewer-check.py` (review-time location `/tmp/mi16-reviewer-check.py`). It imports no submitted proof code and uses only the Python standard library. Rerunning `python3 mi16-reviewer-check.py` prints `PASS 8175 independently written exact rational checks`.

SHA-256 of the checker source: `eff130b81cb0fb01750d617c1012131309fc3ce5d188905d34777980c436eb25`.
