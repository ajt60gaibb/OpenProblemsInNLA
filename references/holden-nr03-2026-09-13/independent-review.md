# Independent informal review of NR-03

**Date:** 2026-09-13. **Reviewer:** separate Codex AI agent, task `nr03_independent_review`, independent of the submitting/editor agent and of the supplied proof/check implementations. This is an informal AI-agent audit, not external human peer review, proof-assistant verification, or certification of novelty.

**Verdict: PASS — complete negative resolution of the original NR-03 target.** Theorem 1 in `NR03_counterexample.tex`, proved in Sections 2–4, establishes

```math
\mathrm{rank}_+(C_n)\le\min\{2^n,2^{n-1}+n+\binom n2+\binom n4\},\qquad n\ge1.
```

In particular, the exact prescribed 128-by-128 matrix has a nonnegative rational factorization with 127 terms at n=7. This disproves the canonical assertion of full nonnegative rank for every n>=3, and the same construction is strictly below full rank for every n>=7. No change of completion, field, quantifiers, or matrix entries is involved. Exact ranks at n=5,6,7 and minimal counterexample dimension are not established and are not necessary to resolve the universal yes/no question.

## Material reviewed

I read the entire submitted TeX, including its appendix and bibliography; the canonical `nonnegative-and-positive-factorizations/NR-03/README.md`; the resolution/status instructions in `CONTRIBUTING.md` and `RESOLVED.md`; the factor generator, integer certificate checker, minimal checker as printed in the manuscript, full test runner and supplementary test source; and `SOURCES.md`. The original supplied TeX SHA-256 was `c394c6618e90c11c3da8f05d21c65accef3fe338a48772e9dcedea18256f5957`; the checked `data/factors_n7.json` SHA-256 was `fa515775f9c77e5dfe85109125d3f730c4b36684894730096247cd67fcc60bb9`. Authorship and review-status editorial updates need not preserve the TeX hash; the mathematical assessment covers the stated formulas and proof.

## Analytic audit

1. **Section 2, equations labeled `eq:denom`–`eq:r`:** one representative omitting coordinate n picks exactly one member of each complementary pair, giving 2^(n-1) atoms. All four families are independent atom indices even if their underlying sets coincide. The pair coefficient 4(p-2) can occur only for p>=2, so every factor entry is nonnegative. The denominator max(1,(p-1)^2) is always strictly positive. Therefore dividing each right-factor column by its denominator preserves nonnegativity and produces rational real factors.
2. **Section 3, equations `eq:G`–`eq:Q`:** with t=|a intersect b| and p=|b|, the pair core is (t-1)^2(p-t-1)^2; singleton correction is 1[p=1](1-t); pair correction is 4(p-2) choose(t,2). For the four-set term, precisely choose(t,3)(p-t) subsets have three elements in a and one outside, while choose(t,4) have four in a, with weights 1 and 2 respectively. This proves the displayed sum 12[(p-t)choose(t,3)+2choose(t,4)] without approximation.
3. **Lemma 1, equation `eq:poly`:** I expanded the factor remaining after division by the formal polynomial factor t(t-1): both sides of the claimed identity are 2pt-2p+t+2-t^2. Consequently the original identity is a polynomial identity and holds also at t=0 and t=1; no illegal numerical division is needed. Replacing falling factorials yields precisely the two correction families. The proof separately handles p=0 and p=1 correctly, so it never uses a zero scaling denominator. Thus WV=C_n D holds at every prescribed entry, including intersections greater than one.
4. **Section 4, equation `eq:pascal`:** q_7=63 and q_(n+1)-2q_n=1-choose(n,2)+choose(n,3)-choose(n,4). For n>=7 the last two terms sum to a nonpositive number, and 1-choose(n,2)<0. This inductively proves q_n<2^(n-1) at every n>=7. The atom counts 127,234,427,777 and the Section 5 numerical slice agree with the formulas.

## Executed checks

The system `python3` is Python 3.9 and lacks `int.bit_count`; its initial attempt to run the suite stopped for that environment reason. The package explicitly requires Python >=3.10. I reran unchanged source using bundled **Python 3.12.14**:

```text
/Users/sholden/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 /private/tmp/nr03-review-input/NR03_counterexample/verify_all.py
```

Exit 0. The construction-independent supplied verifier checked all 16,384 integer-scaled entries, including 5,103 zeros and 11,281 positive entries. The complete suite also passed coefficientwise polynomial checking, all 20,301 integer pairs 0<=t<=p<=200, Pascal/strictness tests through n=1000, certificate regeneration, all 349,524 complete matrix entries for n=1,...,9, rational CSV multiplication against C_7, consistency of CSV/JSON values, and rejection of all six deliberately damaged certificates.

I also wrote `/private/tmp/nr03-independent-check.py` from scratch and ran:

```text
python3 /private/tmp/nr03-independent-check.py
```

Exit 0. This script imports none of the package modules. It validates integer types, nonnegativity, shapes 128-by-127 and 127-by-128, positive denominators, and every stored matrix product entry, calculating intersections through explicit coordinate sets rather than the package's bit-count expression. It independently reconstructs all four contributions using actual subsets and iterates over every row/column pair for n=1,...,7 (21,844 entries). Every reconstructed sum is nonnegative and exactly equals the column-scaled prescribed value. The script is suitable to retain alongside this report; change only its input-directory setting when relocating it. These finite checks support, and do not substitute for, the general analytic argument above. No Lean check was attempted. I did not rerun the optional C++ checks or independently review the nested prior n=4 archive because neither is needed for this proof.

## Sources, provenance and editorial conditions

I independently opened [Vandaele et al., Section 6.4, Conjecture 4](https://arxiv.org/html/1411.7245#S6.SS4) and [Baeckelant et al. v2, Section 6.7 and Appendix A.4](https://arxiv.org/html/2605.14058v2). They support the quoted fixed-matrix conjecture and benchmark context; the v2 header confirms 6 July 2026. The proof itself is elementary and does not depend on those benchmark lower bounds. No exhaustive literature or priority assessment was made.

The submitted TeX has an empty visible author field (line 39) but `pdfauthor={ChatGPT}` (line 36), and Section 7 says the proof and checks were developed in a conversation. The user has explicitly requested Sidney Holden authorship. Add that credit and verified affiliation in the edited submission, while retaining a clear disclosure of ChatGPT assistance and preserving the original archive/provenance record. This review does not independently verify the user's affiliation or attest historical authorship/priority. The archive's statements that no live edit has been made and independent audit is pending describe its original state; current submission notices should record this separate audit accurately. Its reference to the canonical page's September 11 “status check” is imprecise: the supplied canonical page has Last checked September 11 and a September 11 partial-result notice, but the explicitly headed Status check is September 10. Prefer “Last checked” or omit this peripheral wording.

Under `RESOLVED.md` and `CONTRIBUTING.md`, an independently audited complete argument, including AI-agent audit, qualifies for **Solved**. This PASS supplies the mathematical audit for that classification, provided the canonical page preserves NR-03's original target and ID, reports the outcome as negative, cites Theorem 1/Sections 2–4 and this audit, retains earlier partial-result credit as history, and follows the required catalog/PDF/PR procedures. Duplicate/pushed-solution screening, affiliation verification, generated artifact QA and Git submission are the parent agent's separate responsibilities.
