# Independent review of the complete MI-28 proof

> **Metadata-redaction notice (11 September 2026):** The review below records the originally audited versions and their historical hashes. The author subsequently requested removal of email metadata. The final addendum records the redacted file hashes and verifies that every mathematical body is byte-identical. Historical hashes have not been relabeled as current hashes.

**Verdict: PASS.** The reviewed argument establishes the complete canonical positive definite target of MI-28, for every dimension, every real base exponent k >= 0 and every real modulus exponent 0 <= p <= 2. It proves the stronger stated log-majorization as well.

**Reviewer:** independent Codex agent `/root/prepare_manuscripts`.  
**Date:** 11 September 2026.  
**Reviewed canonical manuscript:** [MI-28 solution](../../../../matrix-inequalities-and-norms/MI-28/solution.md).  
**Canonical source SHA-256:** `f173ca333dade27cf98ecc555f294f4d1eabf69a11942b4010342736b233e59b` (12,879 bytes).  
**Canonical mathematical-core SHA-256:** `7e09c48eb306c589e78f31b4ab97cfdd76e2bd6b7fa844779a0bff8b50f27ba1` (9,736 bytes; from `## Statement and notation` inclusive to `## References` exclusive).  
**Original reviewed TeX:** [preserved standalone source](../../original-agent-manuscript.tex).  
**Original TeX source SHA-256:** `cea24a14035f253bd49d88a95c63efaf460bcd19e9e56b5b45ff68bcf809ded1` (13,769 bytes).  
**Original TeX mathematical-core SHA-256:** `2d153a334afff803f352b2002bbe31ed7dffe09e47258d1f748b80835770e229` (9,751 bytes; from the first literal `\section{Statement and notation}` inclusive to the first literal `\Needspace{18\baselineskip}` exclusive).

This is an independent agent review of the analytic proof and its source applications. It is not human peer review, formal proof-assistant verification, a numerical certificate, or a certification of priority. No numerical experiment is used as a premise of the proof. The canonical target and matrix-order conventions were checked against [the retained canonical problem statement](../../../../matrix-inequalities-and-norms/MI-28/README.md).

## Scope and external inputs

The manuscript consistently assumes complex Hermitian positive definite A and B. In particular, all inverses, real spectral powers and positive square roots in the argument exist. With D = |AB|, the identity D^2 = BA^2B is correct without a commutativity assumption. All subsequent congruences use invertible Hermitian factors and preserve the stated order directions.

The Furuta convention used in the manuscript was checked against Propositions 1 and 2 of [Tanahashi, The Furuta inequality with negative powers, primary author-uploaded full text](https://www.researchgate.net/publication/255605812_The_Furuta_inequality_with_negative_powers), p. 1683. Its sandwich exponent is half the manuscript's r. This verifies both the Furuta parameter condition and the range [0,1] for the Löwner–Heinz inequality. The negative-power specialization is proved directly in the manuscript and need not be accepted as a separate unproved input.

For the published k >= 2 range, I checked [Ghabries, Abbas, Mourad and Assi, A proof of a conjectured determinantal inequality, primary author-uploaded full text](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality), Lemma 2.5, on manuscript p. 3. The displayed weak log-majorization and the condition 0 <= t <= s <= K match the final submission. Its use with s = 2 avoids the zero-denominator endpoint of that notation. This previously established part is expressly credited to its authors.

## First order implication

For k > 0 and k/(k+1) <= p <= 1, the choices X = A^k, Y = D^p, r = 2/k, a = 2/p and q = 2 satisfy every Furuta hypothesis. The condition (1+r)q >= a+r reduces exactly to p >= k/(k+1).

The resulting left side is (AD^2A)^(1/2) = ABA: the equality AD^2A = (ABA)^2 is an ordered matrix-product identity and ABA is positive definite. The right side is A^(1+k/p). Congruence by A^(-1), followed by Löwner–Heinz with exponent p, gives the claimed B^p <= A^(k-p). A possibly negative exponent k-p is harmless; the argument does not apply a negative power as an order-preserving operation.

## Second order implication

For k > 0 and 1 <= p <= 2, set s = p(k+2)/(k+p). Direct calculation gives s-p = p(2-p)/(k+p) >= 0 and 2-s = k(2-p)/(k+p) >= 0. Thus q = 2/s >= 1. The Furuta condition holds with equality, and its conclusion is exactly C^s <= A^(k+2), where C = ABA.

The Löwner–Heinz exponent 2/(k+2) lies in (0,1). Applying it and then inverting reverses the order as required, giving A^(-2) <= C^(-2p/(k+p)). With S = A^(-1)C^(1/2), both SS* = B and the singular-value identity (SS*)^p = S(S*S)^(p-1)S* are correct.

Congruence by C^(1/2) and the legal exponent p-1 in [0,1] give a power of C whose exponent is

    1 + (p-1)(k-p)/(k+p) = p(k-p+2)/(k+p).

This is s times theta = (k-p+2)/(k+2), which lies in [0,1]. Applying Löwner–Heinz once more to C^s <= A^(k+2) and then congruencing gives B^p <= A^(k-p). The endpoints p=1 and p=2 are included; no step presumes p-1 is strictly positive or q is strictly larger than 1.

## Parameter interchange and complete coverage

The interchange lemma was independently reconstructed. From D^p <= A^k, define Atilde = D^(-1) and Btilde = B. The noncommuting factor order gives

    |Atilde Btilde|^2 = B D^(-2) B
                      = B(B^(-1) A^(-2) B^(-1))B
                      = A^(-2).

Its unique positive square root is A^(-1). Inverting the premise therefore supplies the exact swapped premise |Atilde Btilde|^k <= Atilde^p. If the universal implication I(p,k) is available, it yields B^k <= D^(k-p). For 0 < p <= k, the exponents p/k and (k-p)/k both lie in [0,1]. Applying Löwner–Heinz first to this conclusion and then to the original premise gives

    B^p <= D^(p(k-p)/k) <= A^(k-p).

The p=k boundary gives an identity in the second step. The reasoning requires neither simultaneous inversion of A and B nor a replacement of |AB| by |BA|.

The integrated manuscript's parameter partition is exhaustive. For 0 < k <= 2, exponents p >= 1 use the second implication. For 0 < p < 1, those with p >= k/(k+1) use the first. Every remaining pair has p < k. If k <= 1, the swapped pair meets the first implication's condition because p/(p+1) < p < k <= 1. If 1 <= k <= 2, the swapped pair meets the second implication's condition. The interchange lemma closes these pairs. Thus the corollary proves I(k,p) throughout 0 < k <= 2 and 0 < p <= 2; it does not merely close a smaller strip.

## Norms, exterior powers and the published range

For fixed A, both H and Z are homogeneous of degree p in B. Since Z is positive definite, its operator norm c is positive. Replacing B by c^(-1/p)B scales both matrices by c^(-1). The normalized condition Z <= I is equivalent by congruence to D^p <= A^k. The order implication gives H <= I after the matching congruence, proving the norm inequality. This step is uniform in dimension and involves no assumption that the input matrices commute.

Exterior powers preserve multiplication, adjoints and the spectral functional calculus for positive definite matrices. In particular, taking the exterior power of the squared modulus and its unique positive square root establishes the displayed modulus identity. The operator norm of the jth exterior power of a positive definite matrix is the product of its j largest eigenvalues. Applying the norm bound in each exterior-power dimension therefore gives all required partial products. The determinant identity follows from det D = det A det B > 0 and supplies equality at the full product.

For k >= 2, the substitution X = A^(-1), Y = B, K = k, s = 2, t = p into the checked published lemma satisfies 0 <= t <= s <= K. Its left product is A^(p-k)B^p, which is similar to H, and its right positive definite matrix is exactly Z because (BA^2B)^(p/2) = D^p. The determinant identity again upgrades the stated weak log-majorization to full log-majorization. No extension of a published parameter restriction is asserted.

## Endpoints and determinant target

At p=0 the two normalized matrices are both A^(-k). For k=0 and fixed p>0, positive k tending to zero remain within the proved k <= 2 range. Functional calculus, ordered eigenvalues and their finite products are continuous, so every majorization inequality and the determinant equality pass to the limit. This includes all the canonical endpoints and n=1.

The logarithms of the positive eigenvalues obey ordinary majorization. The function f(t) = log(1+exp(t)) is convex, with f''(t) = exp(t)/(1+exp(t))^2 > 0. Its sum inequality gives det(I+H) <= det(I+Z). Factoring out A^k on the canonical right-hand side gives det(A^k) det(I+A^(p-k)B^p); the similarity to H is valid and proves this equals det(A^k) det(I+H). The Hermitian side factors by congruence to det(A^k) det(I+Z). Consequently the proof gives the exact canonical inequality, despite the possibly non-Hermitian product A^pB^p.

The optional positive semidefinite extension is limited to positive k,p and follows from the stated simultaneous regularization and continuity. The positive definite theorem itself does not rely on this extension or on a convention for zeroth powers of singular matrices.

No mathematical revision was required by this independent review.

Signed: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026.

## Markdown equivalence audit

**Verdict: PASS.** The standalone Markdown manuscript [preserved standalone Markdown](../../original-agent-manuscript.md) preserves the mathematical content of the frozen TeX manuscript reviewed above.

**Markdown source SHA-256:** `adde305a34b5b53acb3e76c457968bce01cd9690af08fc504a34edde83a9acec` (12,507 bytes).  
**Markdown mathematical-core SHA-256:** `788a1de47b52112c7bbc918d3c6441a8dbeca3cdce6ec81f5a56b2b3b4c954e0` (9,735 bytes; from the literal `## Statement and notation` inclusive to the literal `## References` exclusive).

All 33 displayed formulas, including the abstract's determinant inequality, were compared in order by a separate extraction script. Every pair matches exactly after removing equation labels, alignment wrappers and whitespace, and expanding the two TeX notation macros for log-majorization and the operator norm. The 128 original inline mathematical expressions in the core also match exactly and occur in the same order, after expanding the complex-number, log-majorization and norm macros. Markdown adds five explicit proof-ending squares and four inline references to existing formulas in place of TeX equation-number references. Each such replacement names the correct formula.

I also compared the proof prose, hypotheses, case division, endpoint arguments, attribution and bibliography. No mathematical sentence, restriction, order direction, exponent or conclusion has been omitted or changed. The explicit theorem/lemma/remark numbers 1 through 7 match the shared TeX theorem counter. The author, current Caltech affiliation, email and cited source locations match the reviewed TeX version. The only other changes are the conversion of formatting and cross-references to Markdown, including linked citations and descriptive headings.

This audit applies to the stated Markdown hash before repository metadata or layout-only additions. It does not assert that any later modified file has the same source hash.

Signed: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026.

## Final canonical packaging audit

**Verdict: PASS.** The canonical Markdown proof matches the independently reviewed standalone Markdown mathematical core byte for byte after the sole nonmathematical replacement of the canonical GitHub repository owner, from `MColbrook/OpenProblemsInNLA` to `ajt60gaibb/OpenProblemsInNLA`. Normalizing that owner back gives the original Markdown core hash `788a1de47b52112c7bbc918d3c6441a8dbeca3cdce6ec81f5a56b2b3b4c954e0` (9,735 bytes). All 33 displayed formulas, including the introductory determinant inequality outside the core, are byte-identical to the original Markdown.

The [preserved TeX](../../original-agent-manuscript.tex) and [preserved Markdown](../../original-agent-manuscript.md) are byte-identical to the original files whose hashes and equivalence checks are recorded above. The canonical YAML author, affiliation, email and date metadata agrees with those original sources. Its explicit independent-agent PASS disclosure and limitations accurately describe this review and link to this retained report. The `\pagestyle{plain}` insertion precedes the mathematical core and changes layout only. The bibliography retains the same mathematical sources and locators; only the canonical repository owner changes.

The [reference-package README](../../README.md) correctly describes the proof's scope, imported results, source provenance and independent-agent review. Every relative source, review and canonical-problem link in this report was checked to resolve to the retained repository artifact. No change to the proof, its hypotheses, its mathematical target or its conclusions was required.

Signed: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026.


## Email-metadata removal and final artifact audit

**Verdict: PASS; mathematical content unchanged.** At the author's express request, the email was removed from the canonical manuscript YAML, its generated TeX and PDF, the reference-package authorship paragraph, and the author headers of the retained original Markdown and TeX snapshots. George Stepaniants, the Department of Computing and Mathematical Sciences, and the California Institute of Technology remain stated explicitly. The source snapshots are now metadata-redacted copies of the originally reviewed versions; the historical hashes above remain historical.

The following are the final full-file SHA-256 hashes after that metadata-only change:

- `matrix-inequalities-and-norms/MI-28/solution.md`: `9ef0b68db2072b9d0654a79d75f59f25458660a356693068fa17e334fb1de19c` (12850 bytes). Original full-file hash: `f173ca333dade27cf98ecc555f294f4d1eabf69a11942b4010342736b233e59b`.
- `matrix-inequalities-and-norms/MI-28/solution.tex`: `086bfc3afdcfc7a842ee3b751c7b4a49b297dd0e403ff0c8691bf66806500ace` (15388 bytes). Original full-file hash: `bd779c44afbb6a7cce544d84a7c22c2135eeab87b786a0c2bd5172afff690960`.
- `references/stepaniants-mi28-2026-09-11/original-agent-manuscript.md`: `9bbb7ab7522aa279d5efe3a8fc5406ffe8030aebc1093ca36e2780f3a9859bbf` (12455 bytes). Original full-file hash: `adde305a34b5b53acb3e76c457968bce01cd9690af08fc504a34edde83a9acec`.
- `references/stepaniants-mi28-2026-09-11/original-agent-manuscript.tex`: `bad929b86a301596b881a72040cf2e103a6aa70169a632ba6066d34da262dc6d` (13696 bytes). Original full-file hash: `cea24a14035f253bd49d88a95c63efaf460bcd19e9e56b5b45ff68bcf809ded1`.

The mathematical cores of all four sources are byte-identical to their pre-redaction versions. In particular, the canonical Markdown core remains `7e09c48eb306c589e78f31b4ab97cfdd76e2bd6b7fa844779a0bff8b50f27ba1`, the original Markdown core remains `788a1de47b52112c7bbc918d3c6441a8dbeca3cdce6ec81f5a56b2b3b4c954e0`, and the original TeX core remains `2d153a334afff803f352b2002bbe31ed7dffe09e47258d1f748b80835770e229`. The generated standalone TeX differs from its previously reviewed version solely by deletion of the email line. No hypothesis, formula, proof sentence, mathematical reference or conclusion changed.

The shared solution template now makes the email block conditional, so omission of email metadata produces no empty mail link. The canonical PDF was regenerated by the repository renderer, which reported no overfull boxes or missing characters. The retained original TeX compiled twice with pdfLaTeX without errors, overfull boxes, missing characters or undefined references.

Final canonical PDF: five pages, SHA-256 `2d9cf1edcdd6a30fd0a6f47313d97e4f44fea0277319588ae282cdd32fc91f70`. I rendered and visually inspected all five pages: the author and affiliation remain clear, no email is visible, and the mathematics, page numbers and references are legible without clipping, overlap or missing glyphs. The unchanged problem PDF remains the previously checked two-page file. A separate scan of every newly submitted text/source file, and of both PDFs' extracted text, metadata and annotation links, found no email address.

Signed: Codex agent `/root/review_md03_md04`, 11 September 2026. This is an independent metadata-preservation and artifact check; the mathematical PASS recorded above is unchanged and remains distinct from human peer review or formal verification.
