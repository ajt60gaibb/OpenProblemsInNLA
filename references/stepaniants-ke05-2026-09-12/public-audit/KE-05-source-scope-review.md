# KE-05: source, scope, and prepublication eligibility review

**Verdict: PASS for source/scope matching and this bounded eligibility check.**
This report is a separate Codex-agent review by `/root/prepare_manuscripts`,
completed on 12 September 2026 UTC. It is not the independent mathematical
proof audit, human peer review, or formal verification.

## Exact inputs

The candidate reviewed for scope is `RESULT.md`, SHA-256
`51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f`.
The canonical input was read directly from the public upstream main commit
`1f22006bdaa4659fcaa0bb775a887685cd3cc566`:
[KE-05 original retained target](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/1f22006bdaa4659fcaa0bb775a887685cd3cc566/randomized-and-low-rank-approximation/KE-05/README.md).
Its 4,501 bytes have SHA-256
`ec5086b8ff8215f7445b0c2e185878e09426007d0b721a99b7b814b77e9c065a`
and Git blob `828f9d347e6ce56036933c457518645e94798d42`.
Its status is **Open**. The canonical target, recurrence, and probability
quantifiers were read in full.

## Primary statement and admissibility

[Shao's v2](https://arxiv.org/html/2507.10144v2), dated 30 May 2026,
remains the latest version in the [current arXiv history](https://arxiv.org/abs/2507.10144).
Conjecture 1 in Section 3.2 assumes real diagonal blocks with pairwise
disjoint spectra and a Gaussian block matrix. Theorem 1 gives the prescribed
root ordering and descending recurrence; Section 2.5 and equation (12)
give the endpoint ratios, coefficient normalization, and separate maxima.
These match the canonical definitions. No ordering of the blocks' spectral
intervals is imposed. The scalar-block observation immediately after
(12) explicitly allows repeated eigenvalues within a block. The stronger
separation used in numerical experiments is not a conjecture hypothesis.

For the candidate's fixed family, $0<\varepsilon<1/4$ implies
$0<\varepsilon<2\varepsilon<1<2$. Thus the spectra
$\{2\}$, $\{\varepsilon,2\varepsilon\}$, and $\{0,1\}$ are pairwise
disjoint. The common endpoints are $a=0,c=2$; the first-block minimum
cross-gap is one. Repetition of 2 inside the first block creates no
cross-block intersection. The second spectrum lies inside the interval
spanned by the third; this is admissible and must remain explicit.

The candidate targets the literal canonical random constants. It does not
claim to refute convergence of the block Krylov algorithm or a variant
requiring disjoint, ordered block intervals. Its deterministic sequence
$\varepsilon_m=1/(m+5)$ is independent of the Gaussian draw. Coupling the
same draw across indices only proves a limit of the required marginal
probabilities; it does not strengthen the conjecture's quantifiers.

## Current public eligibility

The fresh API snapshot completed at **2026-09-12 03:13:09 UTC**. It
recursively discovered the original upstream and all five public forks,
including the newly present `yuningyang19` fork. It inspected **47 branch
heads**, representing **41 distinct commits**; **114 selected text blobs**;
**173 issue, PR, and comment bodies**; and **32 PR review bodies** across
all **37 PR review endpoints**. All six repositories have GitHub
Discussions disabled.

Every canonical KE-05 page has the identical Open README blob identified
above. The only KE-05-specific source artifacts found were that page and
its generated TeX; catalog references also remain Open. No matching issue,
PR, comment, or PR review body was found. No alternative KE-05 solution or
mathematical objection appeared in the selected source documents.

The [sanitized snapshot](network-check-sanitized.json) records every
repository, branch, commit, canonical blob, and selected document digest.
It is bound to the private retrieval snapshot SHA-256
`e20fdd63d8b062e1c91e7eb9c4c6367c16dbf1ae1bc64118413ef1e142132c21`.

## Later literature and limits

Exact-identifier, title, author, proof, and counterexample searches found
no posted resolution. The [author's research page](https://sites.google.com/view/nianshao/research)
continues to list the structural-bound preprint. The related
[Chen et al. paper](https://arxiv.org/html/2508.06486), Section 5, retains
an output-bound conjecture involving higher-order gaps; it does not
establish this intermediate-constant claim. The later
[Shao–Nakatsukasa paper](https://arxiv.org/html/2607.10377v1) cites the
structural-bound paper as reference 39, but studies resolvent polefinding
and does not state a resolution of KE-05. See the exact query and source
record in [source-search-record.json](source-search-record.json).

This is a bounded public search, not certification that no unpublished,
private, deleted, unindexed, or unidentifiably named work exists. Selected
branch documents are canonical pages, root indexes, and target/topic-named
text files; arbitrary unrelated file names are outside that content scan.
The mathematical correctness verdict belongs to the separately signed
proof review. No repository, issue, PR, or public status was changed by
this audit. No third-party full source files or contact details are
included in the public audit artifacts.

Signed: **Codex independent source/scope reviewer
`/root/prepare_manuscripts`**, 12 September 2026 UTC.
