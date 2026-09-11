# Solved problems and solution claims

[Open catalog](CATALOG.md) · [Status definitions](README.md#problem-status) · [Report a solution](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/new?template=correction_or_resolution.md)

**Solved problems stay visible.** Their IDs and original statements are retained,
with a prominent status, the resolution reference, its date and exact scope.
They do not contribute to the open count. A counterexample is a solution to a
conjecture's truth question; it is recorded as a negative resolution.

**✅ SOLVED** means the exact target has a published or independently verified
resolution. **🟠 SOLUTION CLAIMED** means a primary manuscript reports a full
resolution whose proof has not been independently verified here. Neither status
is counted as open. A partial result leaves the surviving target in the open
catalog with **🟡 PARTIAL** and an explanation of what remains.

## Resolved catalog entries

### ✅ MF-22 — cubic C1 spline Schrödinger Toeplitz conditioning — George Stepaniants

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology.

**Solved affirmatively, 2026-09-11.** The [Theorem in Section 1 and proof in Sections 2–4](matrix-functions-and-stability/MF-22/solution.md) establish eventual invertibility and $\kappa_2(H_n(\rho))\le K_\rho n$ for every fixed real $\rho>0$. This answers the exact pure Toeplitz question with exponent one, including $\rho=\sqrt{10}$ and all stated boundary entries. [Proof PDF](matrix-functions-and-stability/MF-22/solution.pdf) · [Original canonical target](matrix-functions-and-stability/MF-22/README.md).

The full proof passed a separate [Codex-agent mathematical review](references/stepaniants-mf22-2026-09-11/verification/MF-22-independent-review.md), with an independent checker confirming 31 exact polynomial identities. The [submission record](references/stepaniants-mf22-2026-09-11/README.md) documents substantial AI assistance, the exact reviewed source, public branch/fork checks, and verification limits. This is automated-agent review, not external human peer review or formal verification. The original authors retain credit for the family, root classification and question; the original ID, statement, path and historical ratings remain unchanged.

### ✅ MI-13 — Nobori's spectral-middle-factor commutator inequality

[Original statement and complete proof](matrix-inequalities-and-norms/MI-13/README.md) · [PDF](matrix-inequalities-and-norms/MI-13/problem.pdf)

**Affirmative resolution recorded 2026-09-10.** The complex refined commutator
bound in [Audenaert, Corollary 5](https://arxiv.org/pdf/0907.3913), combined with
square padding and a two-unitary decomposition of a contraction, proves the
exact target for every allowed rectangular dimension. The constant is sharp.
The complete repository proof passed two independent Codex-agent reviews of
its assumptions and steps. It has not received external peer review or Lean
formalization; no novelty claim is made. The former difficulty label remains
historical and the entry no longer contributes to the open count.

### ✅ Five resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Each complete proof passed a separate Codex-agent audit against its exact catalog target on 11 September 2026. Three independent review agents covered the five proofs, with one review per proof. The original drafts were generated in a ChatGPT conversation; the independent agent verification is documented, and no external human peer review or formal proof certificate is asserted. The original statements and historical ratings remain intact. [Review reports, authorship and submission history](references/colbrook-2026-09-11/README.md).

#### IS-02 — negative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/IS-02/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IS-02/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/IS-02/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/IS-02-review.md). **Theorem IS-02, sections 1–2.** The order-four counterexample is real symmetric, nonnegative and stochastic, has spectrum $\{1,1,0,-1\}$ and positive trace, and is spectrally unique up to permutation. It lies outside every segment in the proposed locus, disproving the universal necessary condition at an allowed dimension.

#### SP-04 — negative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/SP-04/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-04/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/SP-04/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/SP-04-review.md). **Theorem SP-04, sections 1–4.** The stationary pair with uniquely smallest absolute multiplier fails to minimize the Frobenius distance on a nonempty open set of real $3\times3$ data matrices with distinct singular values in $(7/4,44/25)$. Both determinant signs are allowed, and the open-set argument refutes the algebraic-generic formulation.

#### SP-05 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/SP-05/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-05/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/SP-05/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/SP-05-review.md). **Theorem SP-05, sections 1–3.** For arbitrary real symmetric positive definite $A,B$, a nonzero real positive-semidefinite eigenmatrix attains the smallest eigenvalue of $X\mapsto AXB+BXA$. Section 3 derives the exact symmetric/skew-symmetric Rayleigh-quotient inequality in the original target, without commutativity, rank restrictions or a simple-eigenvalue assumption.

#### KE-04 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/KE-04/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/KE-04/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/KE-04/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/KE-04-review.md). **Theorem KE-04, sections 1–3.** Strict interval occupancy holds for every allowed pair of block Lanczos iterations and every indicated index, in exact arithmetic before the first loss of full block dimension. The quadratic-polynomial argument includes multiplicities and excludes coincident interval endpoints in the stated range.

#### KE-03 — affirmative resolution

[Original statement and resolution](eigenvalues-and-inverse-problems/KE-03/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/KE-03/solution.md) · [Manuscript PDF](eigenvalues-and-inverse-problems/KE-03/solution.pdf) · [Independent review](references/colbrook-2026-09-11/verification/reviews/KE-03-review.md). **Theorem KE-03, sections 1–5.** The algorithm uses $O(\varepsilon^{-2}[1+\log(nK)])$ exact matrix-vector queries, with success probability at least $0.997$, for every input in the displayed model. It supplies both eigenvalue-location guarantees using the given condition bound $K$ and finite exact arithmetic between queries. The result bounds query count, not total runtime, bit complexity or floating-point error.

### ✅ Three further resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Separate Codex agents checked the complete arguments against the exact catalog targets and returned PASS. Two reviewers covered the three full resolutions; a third checked the related partial bound below. Original AI provenance is preserved, and the verification level is explicitly independent agent review. [Detailed reports and submission record](references/colbrook-additional-2026-09-11/README.md).

#### IS-03 — negative resolution

[Original statement](eigenvalues-and-inverse-problems/IS-03/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IS-03/solution.md) · [PDF](eigenvalues-and-inverse-problems/IS-03/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IS-03-review.md). **Theorem 1 and equations (1)–(7).** The nonnegative real order-seven matrix $A=\operatorname{diag}(1/2,C_2,C_4)$ has a normalized characteristic-polynomial derivative whose seventh power sum is $-8593/823543<0$. Every power of a nonnegative matrix has nonnegative trace, so the derivative cannot be realized at order six, or after any zero padding. Reducibility and positive trace are allowed in the original target. This refutes its universal assertion.

#### SP-06 — negative resolution

[Original statement](eigenvalues-and-inverse-problems/SP-06/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/SP-06/solution.md) · [PDF](eigenvalues-and-inverse-problems/SP-06/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/SP-06-review.md). **Theorem 1 and equations (1)–(8).** The integer-coefficient Laurent polynomial in Theorem 1 is real on a rigorously constructed star-shaped Jordan curve enclosing zero, while its $2\times2$ Toeplitz section has eigenvalues $-128\pm8i$. The proof checks continuity, injectivity and reality on the entire curve. It refutes the conjectured implication for every finite section; it does not refute the distinct limiting-spectrum statement.

#### IE-08 — affirmative resolution

[Original statement](eigenvalues-and-inverse-problems/IE-08/README.md) · [Complete manuscript](eigenvalues-and-inverse-problems/IE-08/solution.md) · [PDF](eigenvalues-and-inverse-problems/IE-08/solution.pdf) · [Independent PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IE-08-review.md). **Theorem 1, Lemmas 2–12 and the final four proof sections.** The end-to-end algorithm uses $O(n^3\log^c(n/\delta))$ arithmetic operations and $O(\log(n/\delta))$ mantissa bits, with universal constants, for every complex input with $\|A\|_2\le1$. With probability at least $0.99$ it returns an exactly upper triangular $T$ and a $Q$ satisfying both displayed residual bounds. The proof includes finite random sampling, deterministic work caps, global recursive conditioning and floating-point error control, without an input separation or diagonalizability assumption. It is an asymptotic existence result with conservative constants, not a production implementation.

**Related partial result — IS-05 (still counted as open).** [Theorems 1–2](eigenvalues-and-inverse-problems/IS-05/solution.md), independently checked in a [separate PASS report](references/colbrook-additional-2026-09-11/verification/reviews/IS-05-review.md), prove the upper bound $\alpha_*\le1/2$ and an additional parity obstruction. The updated interval is $17/92\le\alpha_*\le1/2$; its exact value remains unresolved. [IS-05](eigenvalues-and-inverse-problems/IS-05/README.md) is **Partially resolved**, not Solved.

### ✅ Ten matrix-inequality resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Three independent Codex agents reviewed thirteen complete arguments, with one PASS report per argument. Ten resolve their exact targets and three establish the partial results below. [Authorship, exact scopes, original proofs and reviews](references/colbrook-matrix-2026-09-11/README.md). Verification is independent agent review; the original drafts were AI-assisted.

#### MI-03 — affirmative result

[Canonical entry](matrix-inequalities-and-norms/MI-03/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-03/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-03-review.md). **Theorem 1.1 and its proof.** The sharp additive contraction constant is $c_k=k/4$ for every $k\ge2$, including every odd summand count. Exact dimension-two extremizers match the universal upper bound. 

#### MI-04 — affirmative result

[Canonical entry](matrix-inequalities-and-norms/MI-04/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-04/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-04-review.md). **Theorem 1.1 and its proof.** The universal positive-block operator-norm property holds exactly when the off-diagonal block is essentially Hermitian. The proof applies in every finite dimension without invertibility or distinct-singular-value assumptions. 

#### MI-06 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-06/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-06/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-06-review.md). **Theorem 1.1 and its proof.** No finite constant permits the proposed two-unitary Loewner-order domination for the arithmetic symmetric modulus, already in dimension three. A fixed rational example also refutes the proposed $\sqrt2$ constant. This concerns matrix order, not a separate norm triangle inequality. 

#### MI-07 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-07/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-07/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-07-review.md). **Theorem 1.1 and its proof.** No finite two-unitary domination constant exists for the maximal symmetric modulus, already in dimension two. The rank-one family gives the necessary bound $C\ge\sqrt{1+t^2}/t$ for every $t>0$. 

#### MI-19 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-19/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-19/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-19-review.md). **Theorem 1.1 and its proof.** A real order-four PSD Gram matrix, $q=7/8$ and the interior singleton $S=\{2\}$ give full minus restricted $q$-permanent equal to $-3235575/16384$. Inversions are counted in the full original ordering. The strict counterexample also persists under sufficiently small positive diagonal perturbations. 

#### MI-21 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-21/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-21/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-21-review.md). **Theorem 1.1 and its proof.** Two rational positive definite $2\times2$ summands with $s=t=1/2$, $r=2$ and aggregate matrices $A=B=I$ violate the operator-norm inequality for every $p>0$. The left side has eigenvalue $1351000/1350907>1$, while the right side is one. 

#### MI-22 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-22/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-22/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-22-review.md). **Theorem 1.1 and its proof.** Rational positive definite $3\times3$ matrices at $t=1/8$ violate the first singular-value inequality: the left operator norm exceeds 10900, while $\|AB\|_2<10200$. Exact rational root residuals and a proved operator-root error bound certify the actual principal powers. 

#### MI-23 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-23/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-23/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-23-review.md). **Theorem 1.1 and its proof.** Rational positive definite $3\times3$ matrices with $r=s=1$, $p=2$ and $t=1/8$ violate the corrected eigenvalue log-majorization conjecture. An exact integer-power construction and rational norm separation establish failure of the first ordered eigenvalue inequality. 

#### MI-26 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-26/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-26/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-26-review.md). **Theorem 1.1 and its proof.** The real-valued concave function $f(x)=x-x^2$ and two rational projections refute the two-unitary inequality; an explicit positive definite variant also works. The allowed condition is $f(0)\ge0$, without global nonnegativity or monotonicity. This does not refute the narrower nonnegative-valued function class. 

#### MI-29 — negative result

[Canonical entry](matrix-inequalities-and-norms/MI-29/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-29/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-29-review.md). **Theorem 1.1 and its proof.** A rational positive definite $A$ and invertible indefinite Hermitian $B$ in dimension three, with $k=6$ and $p=8$, reverse the proposed determinant comparison. The exact right-minus-left gap is $21036678407451/156250000000000>0$. The known $k=2$ theorem and the variant $B>0$ are not contradicted. 

#### Related partial results: MI-08, MI-09 and MI-25

These three entries remain in the open count.

#### MI-08 — partial result

[Canonical entry](matrix-inequalities-and-norms/MI-08/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-08/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-08-review.md). **Theorem 1.1 and its proof.** The fixed and adaptive orthogonal pinching lengths both equal the least row count $h(d)$ of a sign matrix $H$ with $H^TH=h(d)I_d$. In particular, the exact length is 12 for $9\le d\le12$. The general value of $h(d)$ is undetermined; the all-dimension optimization remains open and includes Hadamard-order existence questions.

#### MI-09 — partial result

[Canonical entry](matrix-inequalities-and-norms/MI-09/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-09/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-09-review.md). **Theorem 1.1 and its proof.** For every $m\ge2$, the exact dimension-two operator-norm constant is $c_\infty^{\rm sym}(m,2)=\sqrt{6\sqrt3-9}$. This is also the sharp single constant valid simultaneously for every unitarily invariant norm on $M_2$. This does not determine each individual finite Schatten constant. The cases $1<p<\infty$ remain open; the previously established trace endpoint and higher-dimensional operator endpoint are retained.

#### MI-25 — partial result

[Canonical entry](matrix-inequalities-and-norms/MI-25/README.md) · [Complete proof](matrix-inequalities-and-norms/MI-25/solution.pdf) · [Independent review](references/colbrook-matrix-2026-09-11/verification/reviews/MI-25-review.md). **Theorem 1.1 and its proof.** The trace-norm endpoint has $C_1=\infty$: a real $2\times3$ rank-one family has defect ratio asymptotic to $2/(3t)$ as $t\downarrow0$. Zero-row padding gives the same failure on real $3\times3$ matrices. The remaining finite Schatten exponents $1<p<\infty$ are undetermined by this result; the known value $C_2=1$ is unchanged.

### Four resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Three separate Codex agents reviewed the six submitted arguments; the following four resolve exact catalog targets. Verification is independent agent review, not external peer review or formal certification. [Submission record, provenance and reproduction](references/colbrook-transfer-2026-09-11/README.md).

**RA-07 (Solved).** The sequence $(j+1)e_{j+1}/e_j$ is decreasing and discretely convex for every positive spectrum, including both endpoints. The exact second-difference certificate proves the full canonical conjecture.  [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.pdf), Theorem 1.1; [review](references/colbrook-transfer-2026-09-11/verification/reviews/RA-07-review.md).

**RA-08 (Solved).** A rational positive definite $6\times6$ matrix and its exact rank-three Nyström approximation attain the optimal input spectral error but violate transformed optimality for $f(x)=\min(x,1)$. At $t=1/65536$, the output ratio is at least $1+334583/15769728$. Since the input excess is zero, this also excludes every finite factor $1+C\varepsilon$ for that scalar-concave class.  [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.pdf), Theorem 3.1; [review](references/colbrook-transfer-2026-09-11/verification/reviews/RA-08-review.md).

**RA-09 (Solved).** The ordered theorem transfers ordinary relative Frobenius residual error with no loss for the larger monotone subhomogeneous function class. Put $B=\widehat A_k$. Since $0\preceq B\preceq A$, $\|A-B\|_F^2=\|A\|_F^2-\|B\|_F^2-2\operatorname{tr}(B(A-B))\le\|A\|_F^2-\|B\|_F^2$. Thus the original stronger trace-deficit premise implies the proved residual premise, establishing the exact canonical conclusion. All specified eigenbasis choices and zero-tail cases are covered.  [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/02_frobenius_function_transfer.pdf), Theorem 1.1, with the trace-deficit reduction in the entry; [review](references/colbrook-transfer-2026-09-11/verification/reviews/RA-09-review.md).

**RE-05 (Solved).** The nonadaptive two-sided algorithm achieves pure relative Frobenius error with $O(\sqrt{q(\log q+1/\varepsilon)}+\log q)$ queries at constant success. Fifteen independent copies with internal squared parameter $\varepsilon/9$ and the proved median selector give failure at most $e^{-4.8}<0.01$ and norm factor at most $1+\varepsilon$. This meets the exact canonical uniform query bound and arithmetic model.  [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.pdf), Theorem 2.1 and Proposition 5.1; [review](references/colbrook-transfer-2026-09-11/verification/reviews/RE-05-review.md).

#### Related partial result and auxiliary counterexamples

**RA-10 (Partially resolved).** The sharp nuclear relative-excess factor is two when $A$, $B=\widehat A_k$ and the actual selected rank-$k$ projector have a simultaneous orthonormal eigenbasis. The finite-Schatten extension is also proved. Diagonal operator-monotone power examples show that any constant solving the full question must satisfy $C\ge2$. Existence of a finite universal constant for arbitrary noncommuting PSD pairs remains open. Commutation of $A$ and $\widehat A$ alone does not cover every truncation inside a repeated eigenspace. The separate scalar-concave nuclear counterexamples use functions outside the required operator-monotone class. [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/06_commuting_schatten_transfer.pdf), Theorem 1.1 and Section 3; [review](references/colbrook-transfer-2026-09-11/verification/reviews/RA-10-review.md).

**RA-12 (Open).** The submitted Gamma-density examples refute the upper-mode assertion in Hallman Conjecture 1 and the upper-inflection assertion in Conjecture 2, with legally distinct augmentation indices. These are counterexamples to auxiliary assertions. The complete relative Gaussian trace-tail probability chain in this entry is neither proved nor refuted. No revised sharp tail threshold is established; status remains Open. [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/04_gamma_auxiliary_counterexamples.pdf), Proposition 2.1 (with Proposition 3.1 for related evidence); [review](references/colbrook-transfer-2026-09-11/verification/reviews/gamma-auxiliary-review.md).

**RA-13 (Open).** The centered augmented density has a genuine inflection point beyond the proposed auxiliary upper bound. Together with the mode example, this refutes the upper assertions of Hallman Conjectures 1 and 2. The complete absolute Gaussian trace-tail probability chain in this entry is neither proved nor refuted. Failure of an auxiliary sufficient condition does not refute the final tail comparisons; status remains Open. [Complete proof](references/colbrook-transfer-2026-09-11/manuscripts/04_gamma_auxiliary_counterexamples.pdf), Proposition 3.1 (with Proposition 2.1 for related evidence); [review](references/colbrook-transfer-2026-09-11/verification/reviews/gamma-auxiliary-review.md).

### Five factorization resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Three separate Codex agents reviewed all seven arguments; five resolve full canonical targets and two provide partial family results. This is independent agent verification, not external peer review or formal certification. [Submission record and reproduction](references/colbrook-factorization-2026-09-11/README.md).

**NM-03 (Solved).** The exact rational-input decision problem is NP-hard under polynomial-time many-one reductions, even for strictly positive symmetric positive-definite inputs. The proof supplies an inverse-polynomial additive squared-error gap and a polynomial-time rational perturbation to simple spectrum. Factors may be real, exactly as in the canonical question. NP membership and constant-relative-error hardness are not asserted.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NM-03_rank_two_approximation_hardness.pdf), Theorem 1; Theorem 5 and Corollary 6 strengthen the construction; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NM-03-review.md).

**NM-04 (Solved).** The complete Rowland--Wu coefficient identity holds for every positive real rectangular matrix and all $m,n\ge1$. The proof identifies the coefficient sum with one determinant and constructs a null vector after scaling. Vanishing minors and the cases $m=1$ or $n=1$ are included. This proves the displayed coefficients, beyond the previously known algebraic-degree bound.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.pdf), Theorem 1; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NM-04-review.md).

**NR-04 (Solved).** The nine-point matrix $D_{ij}=(i-j)^2$ has nonnegative rank seven, so no exact six-term nonnegative factorization exists. A polygon-contact argument applied to both factors, together with Sylvester's rank inequality, proves the lower bound; an explicit seven-term integer factorization proves the upper bound.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NR-04_nine_point_distance.pdf), Theorem 1, with Theorem 4 for the lower bound; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NR-04-review.md).

**PF-02 (Solved).** A strictly positive integer $6\times6$ matrix has ordinary rank six and real positive semidefinite rank three, while its minimal-factor congruence quotient is disconnected. A continuous congruence-invariant orientation takes opposite signs on two explicit factorizations, proving actual disconnectedness in the required quotient topology. Further constructions cover every factor size $k\ge3$, including strictly positive rational examples by a nonquantitative perturbation argument.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-02_disconnected_orbits.pdf), Theorem 1; Theorem 4 extends the counterexamples to every factor size; [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-02-review.md).

**PF-05 (Solved).** For every real size-two positive semidefinite factorization of an ordinary-rank-three matrix, feasible straight-line infinitesimal rigidity is equivalent to uniqueness up to congruence. The zero-entry argument handles repeated or singular factors and zero rows and columns; the cited positive-entry theorem covers the remaining case. The feasible directions and equivalence group agree exactly with the canonical definitions.  [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-05_rigidity_with_zeros.pdf), Theorem 1, with Theorem 8 for the zero-entry construction; [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-05-review.md).

#### Related partial family results

**NR-03 (Partially resolved).** The fixed three-bit quadratic correlation matrix has nonnegative rank exactly eight. Its ordinary-rank-seven parity null vector constrains both factors in a hypothetical seven-term factorization; nine distinguished entries then exclude such a factorization. The full prescribed-completion conjecture for every $n\ge4$ remains unresolved. The parity restriction is proved only for a hypothetical factorization whose inner dimension equals ordinary rank; it is not imposed on arbitrary wider factorizations. [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/NR-03_n3_exact_rank.pdf), Theorem 1 and Lemma 2; [review](references/colbrook-factorization-2026-09-11/verification/reviews/NR-03-review.md).

**PF-01 (Partially resolved).** The real positive semidefinite rank is exactly four for $n=5$ and $n=6$. Explicit graph factors give the general bound $\operatorname{rank}_{\rm psd}M^{(n)}\le\lceil2\sqrt{2\lfloor(n-1)/2\rfloor}\rceil$, and submatrix monotonicity gives a lower bound of four for every $n\ge5$. The exact ranks as a function of $n$ remain undetermined for $n\ge7$. In particular, the new upper bound five at $n=7,8$ is not accompanied by a matching lower bound five. The finite orders remain part of this single family entry. [Complete proof](references/colbrook-factorization-2026-09-11/manuscripts/PF-01_subset_intersection.pdf), Theorem 1, Corollary 5 and equation (8); [review](references/colbrook-factorization-2026-09-11/verification/reviews/PF-01-review.md).

### Three matrix-function resolutions by Matthew J. Colbrook — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Three separate Codex agents independently reviewed the six manuscripts. [Submission record and reproduction](references/colbrook-matrix-functions-2026-09-11/README.md).

**MF-03 (Solved).** For every integer $m\ge1$, the normalized diagonal Padé denominator for $\cosh\sqrt z$ is nonzero on $|z|\le3$ and $|1-r_m(z)|\le2$ there. The bound is strict for $m\ge2$ and sharp for $m=1$ at $z=3$. The analytic tail argument and exact finite certificates cover every order.  [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.pdf), Theorem 1; [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-03-review.md).

**MF-14 (Partially resolved).** A fixed seven-product scheme has a full-rank complex coefficient map, certified by a nonzero exact integer Jacobian minor. Its image contains a nonempty Zariski-open subset of $\mathbb C[x]_{\le42}$ and is Euclidean dense there. The upper bound excluding degree 43 and above is not proved. The maximal-degree equality remains open; neither exact representation of every polynomial nor real Euclidean dense coverage is asserted. [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-14.pdf), Theorem 1 and equations (1)-(2); [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-14-review.md).

**MF-15 (Partially resolved).** The conventional critical exponent satisfies $\mathrm{CE}_n\ge2n-4$ for every $n\ge3$, already for rational entrywise nonnegative matrices with distinct positive eigenvalues. Combining this with the published upper bound gives $\mathrm{CE}_4=4$. The matching upper bound for every $n\ge5$, and hence the full family equality, remain unresolved. These are conventional matrix powers, not entrywise powers. [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-15.pdf), Theorem 1 and Corollary 4; [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-15-review.md).

**MF-16 (Solved).** The ordinary symmetric two-letter word $XBX^{12}BX=P$ has at least three distinct real symmetric positive definite solutions for explicit integer $B,P$. These are also Hermitian positive definite solutions, refuting the canonical universal uniqueness assertion in dimension two. An exact negative Jacobian determinant and two independent interval implementations certify the counterexample.  [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-16.pdf), Theorem 1; Theorem 4 gives three certified solutions, and Theorem 3 gives a family threshold; [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-16-review.md).

**MF-18 (Partially resolved; auxiliary result only).** For real $A,Q$ with $Q=Q^\top$, scalar regularization $i\eta I$, and a finite invertible stabilizing limit, the manuscript proves that the imaginary-part rank is half the number of odd unit-circle Jordan blocks. It also establishes semisimple regularity and an exact defective example. This does not settle the canonical general complex $C,D,R,P$ problem. Its simple-eigenvalue real subcase was already known; the defective extension is an auxiliary result outside the canonical simple-eigenvalue hypothesis. The existing partial status and general complex target are retained. [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-18.pdf), Theorem 1 and Corollary 3; Section 8 exact defective example; [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-18-review.md).

**SF-01 (Solved).** Every exact Newton square-root iterate initialized at $X_0=A$ remains a real nonsingular H-matrix with positive diagonal. The theorem includes arbitrary positive scalar scaling and nonnegative affine initializations, with one diagonal-dominance weight for all iterates; it also proves the corresponding Halley preservation result.  [Complete proof](references/colbrook-matrix-functions-2026-09-11/manuscripts/SF-01.pdf), Theorem 1; Corollary 5 gives the Halley extension; [review](references/colbrook-matrix-functions-2026-09-11/verification/reviews/SF-01-review.md).

## Reviewed interval and absolute-value submissions - 2026-09-11

Seven exact targets are classified below. Independent agent review is not external peer review; the [submission record](references/colbrook-intervals-2026-09-11/README.md) preserves AI-draft provenance, authorship requested by Matthew J. Colbrook, full source hashes and fresh checks. No priority claim is made. Original IDs and historical ratings are retained. AV-03 and IV-01 are unchanged.

### AV-01 - Affirmative complexity classification

[Original statement](intervals-and-absolute-value-equations/AV-01/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 1 and the algorithm in Section 4 prove polynomial-time recognition of exactly $2^n$ distinct solutions to $Ax+|x|=b$ using $n+1$ rational LP feasibility tests. The result uses rational binary input, has no regularity or finiteness promise, and rejects infinite solution sets. It classifies the displayed decision problem in $\mathsf P$.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/AV-01.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/AV-01-review.md).

### AV-02 - Hardness classification

[Original statement](intervals-and-absolute-value-equations/AV-02/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 2 and Sections 2-3 give a polynomial-time many-one reduction from MAX-CUT to the threshold $c_2(A)\ge t$, using integer upper-triangular matrices with diagonal 2. All queried families are regular. This proves the requested promise-preserving Turing hardness, with equality in the yes case; the restricted rational triangular problem is NP-complete. The result does not assert $\mathsf P\ne\mathsf{NP}$.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/AV-02.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/AV-02-review.md).

### IV-02 - Complexity classification

[Original statement](intervals-and-absolute-value-equations/IV-02/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 1 proves NP-completeness of the upper determinant threshold and NP-hardness of exact determinant-range computation, even for regular independent-entry tridiagonal interval matrices. Section 5 supplies the exact-output upper bound: a polynomial algorithm for the full displayed target exists if and only if $\mathsf P=\mathsf{NP}$. No unconditional separation or strong NP-hardness is asserted.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/IV-02_IV-04.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/IV-02_IV-04-review.md).

### IV-03 - Affirmative resolution

[Original statement](intervals-and-absolute-value-equations/IV-03/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 1 proves that every interval member is inverse-M if and only if the $n^2$ vertices $C-D_iRD_j$ are inverse-M. These are contained in the displayed two-sign family, so the original $2n^2$ equivalence follows. The proof covers all real endpoints, every dimension, zero widths, zero entries and reducible matrices without assuming regularity.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/IV-03.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/IV-03-review.md).

### IV-04 - Complexity classification

[Original statement](intervals-and-absolute-value-equations/IV-04/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 2 proves NP-hardness of exact tridiagonal solution-hull computation even for a regular independent-entry matrix family and the point right-hand side $-e_n$. Section 5 covers the full exact-output convention, including empty solution sets and infinite endpoints, and makes polynomial-time existence equivalent to $\mathsf P=\mathsf{NP}$. It does not unconditionally rule out polynomial time.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/IV-02_IV-04.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/IV-02_IV-04-review.md).

### IV-05 - Affirmative algorithmic resolution

[Original statement](intervals-and-absolute-value-equations/IV-05/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 3 and Sections 3-5 give the exact coordinatewise solution hull using $2n$ rational LPs, each with $n$ variables and $2n$ inequalities, in polynomial binary input length. The construction uses precisely the inverse-M promise and arbitrary interval right-hand sides. Promise recognition is not needed; no solver for the general regular AV-03 problem is claimed.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/IV-05.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/IV-05-review.md).

### IV-06 - Negative resolution

[Original statement](intervals-and-absolute-value-equations/IV-06/README.md). **Solved, recorded 2026-09-11.** Matthew J. Colbrook (University of Cambridge). Theorem 1 gives a $3\times3$ independent-entry interval matrix with at least four components in its real eigenvalue set. Four exact integer eigenpairs at $-3,0,3,25$ and excluded separators $-1,1,12$ refute the universal at-most-$n$ conjecture. No symmetry assumption is introduced, and locating every component endpoint is unnecessary.

[Complete manuscript](references/colbrook-intervals-2026-09-11/manuscripts/IV-06.pdf); [full independent agent review](references/colbrook-intervals-2026-09-11/verification/reviews/IV-06-review.md).

## Reviewed discrepancy submission - 2026-09-11

### MD-06 - negative resolution by Matthew J. Colbrook

[Original statement](matrix-discrepancy-and-optimization/MD-06/README.md). **Solved.** **Negative resolution, Theorem 1.** For a uniformly random labelled simple cubic graph on an even number of vertices, the probability that every local minimum of the homogeneous Kuramoto energy is synchronized tends to **zero**, rather than one. With high probability a nonsynchronized local minimum has edge cosines at least $1/32$ and Hessian at least $(1/320)I$ on the mean-zero subspace. The full analytic argument and the primary random-graph inputs passed two independent agent reviews. The graph model, torus topology and quantification over every local minimum are unchanged.

[Complete primary manuscript](references/colbrook-discrepancy-2026-09-11/manuscripts/MD-06.pdf); [submission and independent review record](references/colbrook-discrepancy-2026-09-11/README.md). Author: Matthew J. Colbrook, University of Cambridge. Verification is by independent agents, not external human peer review. Historical ratings and the original statement are preserved; no priority claim is made.

## Recovered linear-system submissions - 2026-09-11

Eight exact targets passed independent agent review. Author: **Matthew J. Colbrook**, University of Cambridge. [Submission record](references/colbrook-recovered-2026-09-11/README.md) documents the substantial AI assistance, reconstructed sources, full proof hashes and checks. Agent review is not external human peer review or formal certification; no priority claim is made. All original targets and historical ratings are retained.

### IE-13 - Sharp growth classification

[Original statement](linear-systems-and-elimination/IE-13/README.md). **Solved.** Theorem 1 and Sections 2-4 prove $G(0,q)=1$ and $G(p,q)=h_{p+q}$ for $p\ge1$, where $h_t=0$ for $t\le0$ and $h_t=1+\sum_{r=1}^p h_{t-r}$ otherwise. The upper bound covers every complex input and admissible tie path, with growth over all active entries in the fixed original ordering. A real nonsingular matrix of order $2p+q+1$ attains it, including zero upper bandwidth.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-13.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-13-review.md).

### IE-14 - Sharp growth classification

[Original statement](linear-systems-and-elimination/IE-14/README.md). **Solved.** Theorem 1 and Sections 2-4 prove $c_n=F_{n+1}+1$ for every $n\ge4$, with $F_0=0,F_1=1$. The bound covers complex cyclic tridiagonal matrices, every active entry and every permitted GEPP tie path in the original ordering. A rational matrix with both cyclic corners nonzero attains it at every order.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-14.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-14-review.md).

### IE-17 - Negative resolution

[Original statement](linear-systems-and-elimination/IE-17/README.md). **Solved.** Sections 1-4 give one exact full-column-rank $4\times3$ LSMR example for which both displayed errors increase from the first to the second nonzero iterate. The matrix-only spectral backward error satisfies $\mu(x_1)^2\le1979/2000<99/100<\mu(x_2)^2$, and the specified approximation also strictly increases. The right-hand side stays fixed. This settles the canonical spectral-norm formulation; the cited SISC paper uses a different default norm convention, so no Frobenius-error conclusion is inferred.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-17.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-17-review.md).

### IE-18 - Negative resolution

[Original statement](linear-systems-and-elimination/IE-18/README.md). **Solved.** Section 2 refutes the exact four-step identity using $M=\operatorname{diag}(1/10,1/2,3/5)$ and $v=(1,1,1)^T$: the squared norm ratio is $1920682/21289638243>1/14641$, the square of the proposed factor. Both $M$ and $I-M$ are positive definite. Section 3 proves unbounded underestimation over a parameter family. The separate asymptotic convergence question is not resolved.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-18.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-18-review.md).

### IE-19 - Negative resolution and sharp replacement

[Original statement](linear-systems-and-elimination/IE-19/README.md). **Solved.** Section 1 gives an admissible positive symmetric strictly diagonally dominant $3\times3$ matrix with inverse infinity norm $7/9$, below the proposed comparison value $5/4$. Theorem 1 in Section 2 proves that the exact infimum over the displayed class is $1/(\alpha+m)$ for every allowed parameter choice, and strict positivity prevents attainment. The order is entrywise; stronger comparisons of dominance margins are outside the result.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-19.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-19-review.md).

### IE-21 - Affirmative resolution

[Original statement](linear-systems-and-elimination/IE-21/README.md). **Solved.** Theorem 1 and Sections 2-5 prove the displayed Gaussian trimmed-second-moment limit in probability along every sequence $n\to\infty$ and $m/n\to\infty$, with exactly $\lfloor\theta m\rfloor$ retained rows and the variational least singular value. Explicit failure-probability and error bounds are included; no faster aspect-ratio growth assumption is added.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md).

### IE-22 - Affirmative sharp-constant resolution

[Original statement](linear-systems-and-elimination/IE-22/README.md). **Solved.** Theorem 2 and Sections 6-7 prove the sharp constant $c_\theta=\sqrt{h_\theta}$. The upper bound is uniform over all unit-row matrices and even all $m\ge1$ for sufficiently large $n$, with squared normalized error $O_\theta(n^{-1/6})$. Theorem 1 supplies matching spherical realizations along every high-aspect-ratio sequence, proving the exact eventual-uniform optimality quantifiers.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md).

### IE-23 - Negative resolution

[Original statement](linear-systems-and-elimination/IE-23/README.md). **Solved.** Theorem 1 gives a $2\times3$ full-row-rank matrix with distinct norm-minimizing right inverses for every $2<p<\infty$ over both fields. Their common induced norm is $2^{1/2-1/p}$. Sections 3-4 identify the complete minimizer sets, including a complex higher-dimensional family. The smallest matrix is attributed to Dokmanic and Gribonval\'s spectral-norm example; its extension to the displayed direct-inverse objective is checked. No conclusion about the separate product objective is claimed.

[Complete manuscript](references/colbrook-recovered-2026-09-11/manuscripts/IE-23.pdf); [independent review](references/colbrook-recovered-2026-09-11/verification/reviews/IE-23-review.md).

The related order-five rook bound is outside the order-three/order-four target of [IE-15](linear-systems-and-elimination/IE-15/README.md), which remains Open.

## Random cyclic Krylov compression - 2026-09-11

**[IE-10](eigenvalues-and-inverse-problems/IE-10/README.md): Solved.** Theorem 1 proves $\mathbb E\kappa_V(H_k)\leq17n^2k$ for the exact complex-sphere cyclic-shift model. Markov\'s inequality gives the uniform $0.99$ target with $C=1700$ and $c=3$. Sections 5 and 6-7 give two probability proofs; real starts and arbitrary nonnormal inputs are outside the result.

Author: **Matthew J. Colbrook**, University of Cambridge. [Complete proof](references/colbrook-round3-2026-09-11/manuscripts/IE-10.pdf), [independent review](references/colbrook-round3-2026-09-11/verification/reviews/IE-10-review.md), and [submission record](references/colbrook-round3-2026-09-11/README.md). AI generation is disclosed; agent verification is not external human peer review or formal certification. Original target and historical ratings are retained. The accompanying IS-04 prime-square construction remains partial for its all-orders target.

## Accurate polynomial evaluability - 2026-09-11

**[AA-01](arithmetic-and-complexity/AA-01/README.md): Solved.** Theorem 1.1 gives an always-halting decision procedure for the exact constant-free finite-tree model in the statement. In every signed ordering chart $x_{\pi(i)}=\sigma_i(y_1+\cdots+y_i)$, the coefficientwise absolute majorant of $q(y)=p(x(y))$ must be bounded by $C|q(y)|$ on $y\geq0$. This finite real-quantifier criterion is necessary and sufficient; Sections 2-4 prove the equivalence and construct an evaluator when it holds. Both independent reviews cover comparisons, branching, stored-value reuse and arbitrary independent rounding errors.

Author: **Matthew J. Colbrook**, University of Cambridge. [Complete proof](references/colbrook-arithmetic-2026-09-11/manuscripts/AA-01.pdf), [first review](references/colbrook-arithmetic-2026-09-11/verification/reviews/AA-01-review.md), [second review](references/colbrook-arithmetic-2026-09-11/verification/reviews/AA-01-second-review.md), and [submission record](references/colbrook-arithmetic-2026-09-11/README.md). AI assistance and missing experimental sources are disclosed. Agent review is not external human peer review or formal certification. Historical ratings and the exact original target are retained. The accompanying AC-11 and AC-12 finite cases remain partial.

## Published resolutions of historical questions

These questions were screened out before receiving current catalog folders;
they are included here to make their resolutions easy to find. No new problem
IDs or admissions are created by this list. Sources and scope rechecked on
**2026-09-10**.

| Status | Historical question | Resolution and scope |
| --- | --- | --- |
| ✅ **SOLVED** | Higham's growth bound for complex symmetric matrices with positive-definite real and imaginary parts | S. W. Drury, *Fischer determinantal inequalities and Higham's Conjecture*, LAA 439 (2013), 3129–3133, [published result](https://doi.org/10.1016/j.laa.2013.08.031). The bound of two for elimination without pivoting answers the historical below-three question. [Zhang's 2026 paper, §1.1 and Appendix A](https://arxiv.org/html/2604.23024), explicitly traces and refines that result. This does not assert the same bound for arbitrary complex symmetric matrices. |
| ✅ **SOLVED** | Higham's Fréchet-derivative Jordan-form question, *Functions of Matrices*, Research Problem 3.11 | V. Noferini, *The Jordan canonical form of the Fréchet derivative of a matrix function and the bivariate Jordan problem*, [published online in 2026](https://doi.org/10.1016/j.laa.2026.06.002); [primary manuscript, §§4–5](https://arxiv.org/html/2512.08399). The matrix-function problem is answered; the more general bivariate Jordan problem has separate unresolved cases. The journal issue date is October 2026, later than the online publication. |

## Former catalog entries with complete-resolution claims

The classification below concerns the strength of the available evidence, not a
claim that an unrefereed proof is incorrect. The records below were checked
on **2026-09-10**.

<a id="ie-01"></a>

### 🟠 IE-01 — Forsythe's conjecture beyond restart length two

[Original statement and resolution](linear-systems-and-elimination/IE-01/README.md) · [PDF](linear-systems-and-elimination/IE-01/problem.pdf)

Colbrook, Stepaniants and Townsend's [September 2026 preprint, v2, Theorem 1.1](https://arxiv.org/html/2609.04659v2), reports convergence for restart length three and counterexamples for every restart length at least four. This covers the entire former entry. Removed from the open count on September 8; the stable page is restored with the claim prominently displayed. The full proof has not been independently audited by this catalog.

<a id="tr-02"></a>

### 🟠 TR-02 — Greedy cross approximation of the fermionic kernel

The [current workshop report, update after Problem 4.2](https://arxiv.org/html/2602.05394), records V. S. Pendyala's [2026 full-solution claim](https://doi.org/10.5281/zenodo.21863274) for the logarithmic cutoff/accuracy rate. The workshop's report of the claim was checked; the claimed proof itself has not been independently reviewed. The [screening note](references/SCREENED-OUT.md#screened-items-that-are-not-counted) preserves the context.

<a id="re-04"></a>

### 🟠 RE-04 — Finite-family structured approximation with relative error

The [August 2026 update following the abstract of Amsel et al.](https://arxiv.org/html/2507.19290v2) reports an improvement to relative error $1+\varepsilon$ and links an author-endorsed argument. This supersedes its stale question in §5. The [screening note](references/SCREENED-OUT.md#excluded-and-uncounted-leads) records the exact distinction from the still-open linear-family and nonadaptive questions. This catalog has checked the scope of the reported resolution, not independently verified its proof.

### 🟠 Sharp Paulsen bound — proposed FR-12, not admitted

[Lau and Ramachandran, §7, manuscript p. 13](https://arxiv.org/pdf/2510.13751),
announce an optimal unrestricted distance bound in forthcoming work. Their
normalization differs by the frame energy from the usual Parseval formulation;
the announcement addresses the proposed sharp strengthening. The announcement
was independently checked, but its forthcoming proof was not available for
verification. The temporary expansion candidate was withheld and does not
contribute to the open count. Its disposition is recorded in the
[expansion screen](references/EXPANSION-TO-200-2026-09.md).

Other historical exclusions and full-proof claims remain documented in the
[source record](references/SOURCES.md#important-historical-questions-excluded).
This page highlights resolutions and former catalog IDs; it is not a list of
every rejected candidate.

## Recording a new resolution

1. Keep the original problem ID, folder and statement. Do not delete or reuse the ID.
2. Set `**Status:** Solved` or `**Status:** Solution claimed` on its canonical page. Add a prominent resolution notice, a primary reference and theorem/page locator, the resolution date, the outcome (affirmative, negative or classification), and a comparison with the original assumptions and quantifiers.
3. For a partial result, use `Partially resolved` and state the exact remaining cases. A weaker bound, a different algorithm, or a different input model does not settle the target.
4. Add the resolution here, regenerate the catalog indexes with `python3 tools/update_catalog.py`, and regenerate the affected TeX/PDF with `python3 tools/render_problems.py ID`.
5. Submit a pull request. An issue being closed is not, by itself, evidence that a mathematical problem is solved. If a claim is withdrawn or a gap is found, retain the history and revise the status using the new evidence.
