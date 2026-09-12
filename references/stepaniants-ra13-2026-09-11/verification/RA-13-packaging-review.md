# RA-13 exact-source conversion and canonical-scope review

Reviewer: Codex agent `/root/review_aa01`  
Date: 11 September 2026  
Result: **PASS for manuscript conversion and canonical target preservation.**

This is a separate addendum to the original independent proof review. The original frozen proof and its signed review were not modified. This addendum does not claim external human peer review, formal verification, or independent visual PDF inspection; the packaging agent owns the all-page PDF QA.

## Exact files checked

All paths below are relative to the RA-13 worktree `/tmp/nla-ra13-worktree`.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `randomized-and-low-rank-approximation/RA-13/solution.md` | 16027 | `afc1b17cc61164093c5038e786934bc710ef141b9747c9a8a10ca8ab16414677` |
| `randomized-and-low-rank-approximation/RA-13/solution.tex` | 18525 | `8bfde617822abef81989b3c1da94f9390f0e56cad23efaa37f107f91f42e63f9` |
| `randomized-and-low-rank-approximation/RA-13/README.md` | 6070 | `a86d9f1b05b62abcd43c2283878ac3a629a36848d7bb1217575b0675e12fcad6` |

The frozen reviewed proof has SHA-256 `6ee4efe2bf23c91276db20bb2bf67ca05c5fa659f30f50b6f8670fd8507d5dff`. The original independent review has SHA-256 `86f795530bec85ac00e93c6a1fd88b0a2985d49ac38606c2db3c5662b7784b99`.

## The only mathematical-body text corrections

I checked the entire Markdown range from `## 1. Normalized theorem` inclusive through immediately before `## References` exclusive against the same range of the frozen proof. It is byte-identical after exactly these replacements:

1. The two literal `,quad` strings in the definition of M,V,R become `,\quad`.
2. The definition line beginning `u(t)=1-g(z-t)/g(z)` begins `\nu(t)=1-g(z-t)/g(z)` instead.

The second correction identifies the function consistently with the subsequent A0,B0,C0 integrals and measure masses. The original independent review already audited this same function as ν. It is a notation correction, not a new definition or change to any argument.

For the precise range above, including its trailing blank lines, the corrected mathematical body is 13,311 UTF-8 bytes with SHA-256 `9d591a5a403cc418f107b8af9428ba5da87572e2c37b74772a7a04ae4a5d32f9`. No assumptions, inequalities, constants, transfer choices, or limits were added, removed, or changed.

I also extracted all 172 ordered inline and display mathematical expressions from this Markdown body and the corresponding complete TeX body. Every expression agrees after whitespace normalization. I read the complete converted TeX prose and found the arguments, quantifiers, scope restrictions, references, and verification language faithfully retained. Metadata changes consist of the author/affiliation, date, title, review disclosure, and submission references. The manuscript explicitly identifies independent agent review rather than external human review or formal certification.

## Canonical target and auxiliary attribution

The canonical README's entire original range from `## Problem statement` through the end of the file is byte-identical to the pre-resolution page. Thus the probability chain, exact non-strict threshold, all quantifiers, matrix family, Gamma convention, source caveat, and historical source checks are retained. The permanent ID and canonical path remain RA-13.

The new resolution paragraph states exactly the scope established by the independently reviewed proof: both comparisons, nonzero real symmetric matrices including indefinite and zero-trace cases, positive sample counts, and the endpoint threshold. It links the complete proof and the independent review.

Matthew J. Colbrook's auxiliary counterexamples, mathematical claims, manuscript links, and review attribution remain present. Only their obsolete current-open wording is replaced with a historical-scope statement distinguishing those auxiliary results from the new full probability-chain proof. This is accurate: the new proof does not revive the refuted general auxiliary conjectures.

The checked author metadata names George Stepaniants and the Department of Computing and Mathematical Sciences, California Institute of Technology, with geographical affiliation. No personal email is introduced. This review does not certify the separate public-network audit or perform staging, committing, pushing, or pull-request creation.
