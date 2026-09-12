# Independent review of the KE-05 negative solution

**Verdict: PASS for a complete negative answer to the literal canonical KE-05 target. No mathematical correction is required.**

Reviewer: Codex agent `/root/review_aa01`, distinct from the proof-drafting agent `/root/review_md03_md04`. Date: 12 September 2026 UTC. This is an independent agent audit, not external human peer review or formal proof-assistant certification. It does not certify novelty or the absence of another public submission.

## Exact version reviewed

I read the entire frozen candidate, independently reconstructed its argument, and checked the precise canonical assumptions against the primary source.

- Author candidate: `/tmp/nla-fresh-round11/ke05-negative/RESULT.md`, **13,461 bytes**, SHA-256 `51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f`.
- An unchanged portable copy is [reviewed-proof.md](reviewed-proof.md), with the same size and hash.
- The exact target snapshot is [canonical-statement.md](canonical-statement.md), **4,501 bytes**, SHA-256 `ec5086b8ff8215f7445b0c2e185878e09426007d0b721a99b7b814b77e9c065a`.

Before this audit I had a separate bounded assignment to scan clustered spectra using the literal recurrence. That scan found other apparent divergent families. I stopped it when assigned this review. The scan is not evidence for the proof below and is not imported by the independent checker. I did not write or revise the analytic candidate, and I did not read or reuse its author's checker. The coordinating agent supplied an outline; I did not treat that outline or its preliminary verdict as evidence.

## 1. Target and primary-source scope

The canonical quantifiers permit all real diagonal blocks with pairwise disjoint spectra, allowing repetitions within an individual block. A counterexample for the fixed pair b=2,d=3 is enough to disprove the universal assertion; the manuscript is not required to classify every b,d.

I directly read the current [Shao primary text, arXiv:2507.10144v2](https://arxiv.org/html/2507.10144v2), dated 30 May 2026: Lemma 3, the recurrence and reordering in Theorem 1, equation (12), and Conjecture 1 in Section 3.2. These match the canonical definitions. Conjecture 1 imposes disjoint spectra, without requiring that the blocks occupy disjoint ordered intervals. The two constants in (12) are maximized separately over the prescribed orderings. The current [arXiv record](https://arxiv.org/abs/2507.10144) was also checked.

Thus the input

\[
 \Lambda_1=2I_2,\qquad \Lambda_2=\operatorname{diag}(\varepsilon,2\varepsilon),
 \qquad\Lambda_3=\operatorname{diag}(0,1),\qquad0<\varepsilon<1/4
\]

is fully admissible. It uses a repeated eigenvalue only inside the first block and an interlacing of the latter two blocks that the hypotheses permit. Global endpoints are a=0,c=2. The proof concerns the defined constants; its scope paragraph correctly avoids claiming a counterexample to the output convergence of a Krylov algorithm.

## 2. Literal recurrence and the transformed block

I reconstructed the k=1 order directly, preserving product order throughout. Write X=Ω₂⁻¹diag(1,2)Ω₂ and P=Ω₃⁻¹diag(0,1)Ω₃. The descending recurrence gives

\[
 \widehat B_3=P,\qquad S_{2,3}=\varepsilon X-P=:T,
 \qquad\widehat B_2=T^{-1}\varepsilon XT.
\]

These formulas follow from the canonical Ω-hat definition because
(ΩᵢS)⁻¹Λᵢ(ΩᵢS)=S⁻¹BᵢS. They do not depend on a source formula for fundamental matrix polynomials.

For a rank-one idempotent P, tr P=1, det P=0, and adj P=I−P. In dimension two the adjugate is linear, and the determinant polarization is symmetric. Consequently, with κ=tr((I−P)X),

\[
 \det T=\varepsilon(2\varepsilon-\kappa),\qquad
 \widehat B_2=
 \frac{(\varepsilon\operatorname{adj}X-(I-P))X(\varepsilon X-P)}
 {2\varepsilon-\kappa}.
\]

I checked both identities directly. If κ≠0, the denominator is nonzero for all sufficiently small positive ε. The limiting matrix is

\[
 N=-\frac{(I-P)XP}{\kappa},
\]

and N²=0 because P(I−P)=0. A nonzero nilpotent limit is consistent with both eigenvalues of the similar matrix tending to zero; no normality is assumed.

An additional independent algebraic reconstruction used a basis in which P=diag(0,1). For an arbitrary matrix X=[[a,b],[c,d]], the determinant is ε(εdet X−a), and the limit is [[0,−b/a],[0,0]]. This verifies the noncommutative formula on the full relevant similarity class. I did not assume this change of basis preserves a spectral norm; only the exact matrix identity and nonzero character are used that way. Norm limits are taken in the original fixed coordinates.

## 3. Almost-sure nonzero limit

The manuscript's rational witness is correct. With Ω₂=I and Ω₃=[[1,2],[3,5]], direct rational arithmetic gives

\[
 P=\begin{pmatrix}6&10\\-3&-5\end{pmatrix},\quad
 \kappa=7,\quad
 (I-P)XP=\begin{pmatrix}30&50\\-18&-30\end{pmatrix}.
\]

Thus the two rational functions κ and Q₁₁ have numerator polynomials that are not identically zero after clearing powers of det Ω₂ and det Ω₃. The common Gaussian law on the eight matrix entries is absolutely continuous. Each nonzero polynomial's zero set is null, as is the singular-matrix set. The proof correctly concludes κ≠0 and Q₁₁≠0 almost surely, hence ||N||₂>0 almost surely.

A single exact witness is sufficient for this nonidentity argument; it is not being presented as an event with positive Gaussian probability. The full displayed formula for the witness's transformed block was checked, including its off-diagonal signs. Its limiting spectral norm is 68/7: N has rank one and its squared Frobenius norm is 4624/49.

## 4. The coefficient factor does not cancel the divergence

The chosen monomial ratio uses a=0 and i=2 in the k=1 ordering. It is exactly ||B-hat₂||₂/(2ε), so no 0/0 convention enters this lower bound.

I independently computed the root gap:

\[
 \min\{2-\varepsilon,2-2\varepsilon,2,1\}=1.
\]

The fact that B₁=2I is scalar makes the literal recurrence

\[
 S_{1,2}=2I-\widehat B_2,\qquad
 S_{1,3}=(2I-\widehat B_2)(2I-P).
\]

This factorization retains the required order. Similarity of B-hat₂ to diag(ε,2ε) and the spectrum {0,1} of P give

\[
 \det S_{1,3}=2(2-\varepsilon)(2-2\varepsilon)\in(0,8).
\]

For any invertible 2×2 S, the singular-value inequality
||S⁻¹||₂≥|det S|⁻¹ᐟ² is correct. The canonical exponent 1/(d−1)=1/2 therefore yields

\[
 \chi_{\rm coef}\ge\chi_{\rm coef}^{(1)}
 =\|S_{1,3}^{-1}\|_2^{1/2}\ge8^{-1/4}.
\]

The separate global maxima can only increase these two lower bounds. The argument does not need the same ordering to attain either global maximum, and in fact both lower bounds already come from k=1.

## 5. All inverse requirements and exceptional cases

I checked Section 4's genericity proof for the entire prescribed recurrence, not only for the two factors used in the lower bound.

For each fixed ε and each prescribed reordering, setting every Ωᵢ=I makes all blocks diagonal and gives Sᵢⱼ as the diagonal product of cross-block differences. Every diagonal factor is nonzero by pairwise disjointness. This includes the repeated entries of Λ₁: the recurrence compares different blocks, never distinct entries within that block.

Each later inverse is a rational operation in the original Gaussian entries. Clearing all earlier nonzero denominators yields a determinant numerator that is nonzero at the all-identity witness. Induction over the finite list of inverses therefore bounds the exceptional set by a finite union of nonzero-polynomial zero sets. It is null. This is valid independently of the general ordered-product assertions in the source.

There are finitely many root orderings and countably many deterministic εₘ=1/(m+5). Taking their null-set union is legitimate. It follows that every prescribed constant is defined for every member of the sequence on one probability-one event. The endpoint convention handles any scalar 0/0 ratio elsewhere, without affecting the lower bounds. Extending the constants arbitrarily on the null exceptional sets is measurable and does not change their distributions.

## 6. Probability quantifiers and completeness of the disproof

Coupling all inputs with a common draw of the three Gaussian matrices is permissible: for each fixed deterministic εₘ the marginal law is exactly the canonical one. No eigenvalue is selected after observing the randomness.

On a probability-one event, all inverses are defined on the sequence and B-hat₂(εₘ)→N with ||N||₂>0. Consequently

\[
 \chi_{\rm mono}(\varepsilon_m)\chi_{\rm coef}(\varepsilon_m)
 \ge \frac{8^{-1/4}\|\widehat B_2(\varepsilon_m)\|_2}{2\varepsilon_m}
 \longrightarrow\infty.
\]

For each finite deterministic threshold C, the indicator of the event that this product is at most C tends almost surely to zero. Bounded convergence then proves that its marginal probability tends to zero. A claimed spectrum-uniform C(2,3,1/2) would keep every such probability at least 1/2, an immediate contradiction.

This is the required failure of uniform boundedness in probability, not merely failure of a simultaneous-in-spectrum guarantee for one draw and not merely a large value at a single rational Ω. The stronger probability limit claimed in the candidate is established. All assumptions of the original target are retained.

## 7. Independent exact verification

I wrote and ran [independent_exact_check.py](independent_exact_check.py), using only Python's standard library. It imports neither the author's checker nor the earlier partition scan. The accompanying [output](independent-exact-output.json) reports PASS.

The checker verifies three universal identities over the polynomial ring Q[ε,a,b,c,d] with P=diag(0,1): the determinant, the numerator's leading coefficient after the ε cancellation, and the root-determinant identity after clearing rational denominators. It separately verifies the nonorthogonal rational witness, its nonzero nilpotent limit, and twelve finite literal recurrence instances (all three orderings at four rational ε values). The universal algebra and hand audit establish the general formula; the finite instances are supplementary transcription checks and are not substituted for the probability proof.

- Checker: **5,190 bytes**, SHA-256 `ef041d1bbbc62dbcfb94f7f8482eac552202799fb6d9286edaaf35c212d2383d`.
- Output: **3,450 bytes**, SHA-256 `9653a7b37f6656c729eb694d9e48efed476693378e6b601509cfe54359e6d865`.

The checker reads the adjacent immutable `reviewed-proof.md` and verifies its exact hash before reporting success. Reproduce with `python3 independent_exact_check.py` from any working directory. The complete review bundle's file fingerprints are in `manifest.json`.

## Decision and limits

**PASS: the frozen manuscript completely disproves canonical KE-05.** No amendment to its mathematical argument is requested. Repeated within-block eigenvalues, interlaced spectra, every prescribed reordering, probability-zero failures, separate marginal probability quantifiers, and the coefficient normalization are all handled correctly.

This audit does not verify a broader claim about Krylov convergence, external human peer review, formal certification, novelty, or public submission eligibility. A final typesetting/conversion audit should separately bind any eventual publication artifacts to this reviewed mathematical source.

## 8. Publication Markdown binding

After the complete mathematical audit above, I independently compared the prepared public Markdown at `/tmp/nla-ke05-worktree/randomized-and-low-rank-approximation/KE-05/solution.md` against the frozen candidate and read its publication wrapper and entire scope section. This additional check is **PASS**.

- Prepared public `solution.md`: **14,018 bytes**, SHA-256 `31c3416ba212cb2cbb73d126633efe79f1e4a2669a80ef5936fa12dc6723bd62`.
- The range beginning `## Exact target and conclusion` and ending immediately before `## Scope, attribution, and verification limits` is **11,073 bytes**, SHA-256 `ead1a59b806a5f47c8f8c5c4a251a8195ebd66bd527ef1653362acd1df8d7bdd`, byte-identical in the reviewed and prepared manuscripts.
- The wrapper adds George Stepaniants's name, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, date, Shao attribution, and explicit AI-assistance/review limitations. It correctly distinguishes the contributing coordinating agent from the independent reviewer and contains no contact email.
- The mathematical scope paragraphs are unchanged. The end of the verification paragraph now refers to the linked reviews and eligibility audit, and the canonical reference points to the upstream `ajt60gaibb` repository. These changes do not strengthen the mathematical claim. This review does not independently certify that the external eligibility audit has completed.

Exact comparison evidence is [publication-source-comparison.json](publication-source-comparison.json). The public Markdown remains frozen under the hash above; I made no change to it. This binding does not yet cover generated TeX/PDF layout or a changed canonical README, which require their own final artifact checks.
