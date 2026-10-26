# Tensor-problem manuscripts by Matthew J. Colbrook — 11 September 2026

**Author:** Matthew J. Colbrook.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
**Email:** m.colbrook@damtp.cam.ac.uk.  
**Development and review date:** 11 September 2026.

These are new proofs developed with AI assistance in the current repository work at the author's request. They are not recovered files from a missing submission archive. The byline and affiliation follow the authored manuscripts. No novelty, priority, external human peer review or formal verification is claimed.

## Manuscripts and independent verification

TR-06 and TR-15 received PASS verdicts from a separate Codex review agent, which read their complete sources, checked the exact canonical assumptions and quantifiers, and consulted the primary references. The same independent reviewer covered these two manuscripts. Each report records the SHA256 of the complete reviewed UTF-8 source with CRLF replaced by LF and no trimming. Numerical or finite symbolic checks are supporting diagnostics, not substitutes for universal proofs.

TR-06 also passed a [second independent complete-source review](verification/reviews/TR-06-second-review.md). TR-26 passed a [separate independent final review](verification/reviews/TR-26-review.md) by an agent that did not develop its proof. All three exact canonical targets are therefore recorded as Solved under the repository's independent-verification rule. The complete manuscript sources remain unchanged after review.

| Canonical target | Outcome and verification | Complete manuscript and locator |
| --- | --- | --- |
| [TR-06](../../tensor-computations/TR-06/README.md) | Affirmative resolution; [independent PASS report](verification/reviews/TR-06-review.md) | [TR-06 manuscript](manuscripts/TR-06.md), theorem in §1, proof in §§2–4 |
| [TR-15](../../tensor-computations/TR-15/README.md) | Negative resolution; [independent PASS report](verification/reviews/TR-15-review.md) | [TR-15 manuscript](manuscripts/TR-15.md), Counterexample proposition and proof; optional existence argument |
| [TR-26](../../tensor-computations/TR-26/README.md) | Affirmative resolution; [independent PASS report](verification/reviews/TR-26-review.md) | [TR-26 manuscript](manuscripts/TR-26.md), Theorem 1, Lemmas 2–6 and §§2–7 |

## Exact scopes

**TR-06.** For every order $d\ge3$, mode sizes $n_j\ge2$ and rank $r\ge3$ satisfying generic complex identifiability, the mean angular condition number is finite under induced Euclidean volume weighted by $\exp(-\|A\|_F^2/2)$ on the smooth identifiable real rank-$r$ locus. The angular condition number is the operator norm of the derivative after individually normalizing the recovered rank-one summands. The proof handles local labeling, a full-measure regular locus and integration near both degeneracies and the cone vertex. It makes no claim about independent Gaussian summands, the ordinary condition number, higher moments or a format-uniform numerical bound.

**TR-15.** At $m=3$, $q=2$, $n=2$, the common Hankel generating vector $(2,0,1,0,2,0,-1)$ gives an order-three tensor of dimension three with every real H-eigenvalue strictly positive, and an order-six tensor of dimension two with H-eigenvalue $-1$. An additional exact existence argument makes the premise nonvacuous. This single allowed instance disproves the universal odd-order inheritance assertion. It does not challenge the even-lower-order theorem or impose the stronger positive-semidefinite associated-matrix hypothesis.

**TR-26.** For every $d\ge2$, the standard unweighted rational normal curve $[a^d:a^{d-1}b:\cdots:b^d]$ over $\mathbb C$, with the bilinear quadratic form $z^\top z$, has reduced isotropic and nonisotropic Rayleigh–Ritz discriminant degrees $2d$ and $6(d-1)$, respectively. The proof identifies $2d$ distinct isotropic hyperplanes and an irreducible nonisotropic hypersurface, including multiplicities in the full discriminant, infinity, the smallest degree and the numerator-map kernel. It does not claim the same result for weighted embeddings with repeated denominator roots.

## Primary references and provenance

1. C. Beltrán, P. Breiding and N. Vannieuwenhoven, *The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*, Foundations of Computational Mathematics 23 (2023), 433–491. [Journal DOI](https://doi.org/10.1007/s10208-022-09551-1), equation (6), Theorem 3 and Conjecture 2; [primary preprint](https://arxiv.org/pdf/1903.05527), Definition 1.3 and Conjecture 1.10. These specify the TR-06 model and target.
2. R. Hardt, P. Lambrechts, V. Turchin and I. Volić, *Real homotopy theory of semi-algebraic sets*, Algebraic & Geometric Topology 11 (2011), 2477–2545. [Published article](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf), Theorem 2.4, supplies the bounded-semialgebraic-set finite-volume result used in TR-06.
3. W. Ding, L. Qi and Y. Wei, *Inheritance properties and sum-of-squares decomposition of Hankel tensors: theory and algorithms*, BIT Numerical Mathematics 57 (2017), 169–190. [Journal DOI](https://doi.org/10.1007/s10543-016-0622-0); [author PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), final §4, gives the odd-order inheritance conjecture addressed by TR-15.
4. V. Borovik, H. Friedman, S. Hoşten and M. Pfeffer, *Numerical Algebraic Geometry for Energy Computations on Tensor Train Varieties*, [primary preprint v2](https://arxiv.org/html/2512.06939v2), 18 June 2026, §3.2, Propositions 3.6–3.10 and Conjecture 3.14. This supplies the exact target checked in the independent TR-26 review.

The original canonical problem statements, permanent IDs and historical ratings remain retained. TR-06, TR-15 and TR-26 are recorded as Solved on the strength of independent agent proof review, with the verification level stated explicitly. Any later substantive manuscript revision requires a corresponding review update tied to the revised complete source.

## Supplied archive and preserved evidence

All 18 files from `tensor_computations_everything.zip` are retained byte-for-byte under [submitted](submitted/). The [archive manifest](verification/archive-manifest.json) records the archive hash, every extracted file hash, safe-path checks, and successful validation of both supplied checksum lists (17 outer and 15 inner entries). The 16 inner files match the preceding tensor archive. Its own contents notice confirms that the referenced manuscripts, preamble and verifier were not included. No supplied program was executed. The archive summaries alone are not treated as independently verified proofs, and no other IDs advertised there are marked solved by this submission.

The [claim inventory](verification/claim-inventory.json) records the public upstream/fork branches and issue/PR search. No public TR-06, TR-15 or TR-26 solution claim was found in that search. This does not establish historical priority or cover private and unpublished work. [Official Cambridge affiliation](https://www.damtp.cam.ac.uk/user/mjc249/home.html) checked 11 September 2026.

## Reproducible documents and checks

Each manuscript has a standalone [TR-06 PDF](manuscripts/TR-06.pdf), [TR-15 PDF](manuscripts/TR-15.pdf), or [TR-26 PDF](manuscripts/TR-26.pdf), with TeX beside its Markdown source. Run `python verification/build_manuscripts.py` from this record (with Pandoc and XeLaTeX installed) to rebuild them; the builder first verifies each complete source against its independent review hash. Optional executable paths use `PANDOC` and `XELATEX`.

Run `python verification/check_tr15.py` for the exact integer contraction and positivity-identity checks; [results](verification/TR-15-exact-checks.json) are retained. The universal TR-06 and TR-26 proofs use no computational experiments. Canonical README/PDF/TeX, catalog updates and RESOLVED entries preserve all original targets and permanent IDs. [Document and safeguard checks](verification/document-checks.json) record final validation.
