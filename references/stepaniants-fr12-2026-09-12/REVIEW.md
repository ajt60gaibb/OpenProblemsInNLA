# FR-12 independent mathematical review

**Verdict: PASS for a complete negative answer to the exact canonical FR-12
counting conjecture.** The reviewed construction is injective, its iteration
proves the displayed lower bound at every power-of-two order, and that
infinite subsequence contradicts the conjectured universal upper bound.
No mathematical correction is required in the exact source reviewed below.

Reviewer: independent mathematical-review agent `/root/review_aa01`.
Review date: 12 September 2026 (UTC). This is a separate AI-agent audit,
not human peer review, formal verification, or certification of historical
priority. The reviewer did not author or alter the candidate. The
coordinating agent supplied an outline and asked for adversarial review;
I read the entire frozen LaTeX, independently reconstructed the proof,
checked the original published target, and wrote a separate exact checker
without importing the author's checker.

## Exact version binding

Reviewed user source: [reviewed-proof.tex](reviewed-proof.tex), copied
byte-for-byte from `/tmp/nla-fr12-candidate/original-user-source.tex`.

SHA-256:
`efbcaeb82adc140be98cdffca39bf9d9a34d3b281951f42c9d7f7232279335ba`.

Canonical target snapshot: [canonical-target.md](canonical-target.md),
from `frames-and-matrix-designs/FR-12/README.md` in the supplied worktree.

SHA-256:
`75985085b1cd29b2a9358692adb1573ab5c454f0befd4d991e023f37cc6cd942`.

This report applies to those exact files. Publication metadata or review
status may appropriately be updated in a separate public wrapper, while
the reviewed original should be preserved. Any mathematical conversion
should receive a separate source-preservation check.

## 1. The original target is the one disproved

I independently read Ferber--Jain--Zhao's published paper, *On the number
of Hadamard matrices via anti-concentration*, Combinatorics, Probability
and Computing 31 (2022), 455--477, specifically the definition/counting
paragraph and Conjecture 1.3 on printed p.456 (PDF page 2).

The paragraph counts distinct sign matrices and uses row permutations
to obtain a lower bound; it is not a count modulo signed row/column
permutations. Conjecture 1.3 asks for an upper bound of order
2^{O(n log n)} at orders divisible by four. This agrees with the canonical
explicit formulation: one absolute C with H(n)<=2^{C n log_2 n} at every
positive such n.

Primary publication:
https://doi.org/10.1017/S0963548321000377

Primary published full text:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/887EFBBF79B804BCDD942029283D4CD7/S0963548321000377a.pdf/on_the_number_of_hadamard_matrices_via_anticoncentration.pdf

The arXiv record https://arxiv.org/abs/1808.07222 identifies the earlier
2018 v1 manuscript; the review's mathematical scope is tied to the
published Conjecture 1.3 rather than relying on its earlier numbering.

Thus a super-n-log-n lower exponent along powers of two suffices for the
full requested negative answer. It is not necessary to construct matrices
at every order divisible by four, determine the actual asymptotic count,
or replace the conjecture with a matching upper bound. The candidate
correctly distinguishes this counting problem from the existence problem.

## 2. Construction and orthogonality

For a positive integer m, choose any A,B in the set of labeled m-by-m
Hadamard matrices and any perfect matching of the 2m labeled output rows.
Orient each pair by its smaller label and order pairs by their smaller
labels. These are deterministic conventions, not additional choices.

The two rows assigned to pair i are (A_i,B_i) and (A_i,-B_i). All entries
are signs. Their squared norms are 2m. The inner product within the pair
is ||A_i||^2-||B_i||^2=m-m=0. Between different pairs i and j, a row inner
product is A_i dot A_j plus or minus B_i dot B_j, and both summands vanish.
Therefore the output C obeys CC^T=2m I_(2m).

This calculation uses only the separate row orthogonality of A and B.
There is no missing condition such as AB^T=0, commutativity, compatible
normalization, or a relation between their equivalence classes. The fact
that A and B are arbitrary independent labeled Hadamard matrices is
therefore legitimate.

The argument includes m=1. If a particular order m has no Hadamard
matrix, the construction's domain is empty and its counting inequality
is still true; the subsequent logarithms are used only at orders whose
existence has been explicitly established.

## 3. Adversarial collision audit

The central issue is whether changing the matching, signs, or input row
orders can produce the same labeled output. The candidate gives a complete
inverse on its image:

1. Partition the labeled rows of C by equality of their first m entries.
   Every A_i appears exactly twice. Distinct rows A_i,A_j cannot be equal,
   since equality would give inner product m instead of zero. Thus each
   equality class has exactly two members and is exactly an input pair.
2. Recover the canonical orientation and order directly from those row
   labels: smaller member first, pairs sorted by their smaller members.
3. Read the first half of the smaller row in pair i to recover A_i, and
   its last half to recover B_i.

This reconstruction returns the entire ordered matrices A and B and the
matching, including all signs. It proves injectivity on the full domain,
not merely on normalized matrices or on a chosen equivalence-class
representative family.

Row permutations of the inputs do not create a residual ambiguity: once
the output matching is recovered, its canonical pair ordering fixes which
input row is row i. Swapping the two rows of a pair changes the recovered
B_i sign and therefore changes the input triple unless all corresponding
labeled output entries also agree, in which case the inverse already
returns the same input. Signed-permutation symmetries of a Hadamard matrix
are irrelevant because actual labeled entries are retained throughout.

The count of perfect matchings is (2m)!/(2^m m!), since an ordered list of
all labels describes each unordered matching exactly 2^m m! times.
Together with injectivity this gives, for every positive m,

H(2m) >= (2m-1)!! H(m)^2.

No division by an unproved bound on an automorphism group appears.

## 4. Iteration and all-constant contradiction

The construction recursively supplies at least one Hadamard matrix at
every power of two, starting with an order-one sign matrix. Therefore
H(2^k)>0 and a_k=2^{-k} log_2 H(2^k) is defined.

For k>=2, put m=2^{k-1}. Then m is even and

(2m-1)!! = product_(j=1)^m (2j-1) >= m! >= (m/2)^{m/2}.

The first comparison is termwise, since 2j-1>=j. The second keeps the
largest m/2 factors of m!, each at least m/2; discarded factors are at
least one. The m=2 endpoint is harmless.

Dividing the logarithm of the recurrence by 2m gives exactly

a_k >= a_(k-1) + (log_2 m-1)/4 = a_(k-1)+(k-2)/4.

The source uses only a_1>=0, which follows already from existence (and
is much weaker than the exact H(2)=8). Summing from 2 through k gives

a_k >= (k-1)(k-2)/8,

hence H(2^k)>=2^{2^k(k-1)(k-2)/8}, including k=2 where the bound is
weak but valid.

For any proposed fixed C>0, choose an integer k greater than both 2 and
8C+3. Then (k-1)(k-2)/8>Ck. At n=2^k, a positive multiple of four, the
candidate's lower bound is strictly larger than 2^{C n log_2 n}.
This is an all-C contradiction on an explicit infinite sequence of
admissible orders. It proves the complete negation of the target, rather
than merely violating a suggested numerical value of C.

The proven exponent has order n(log n)^2 on that subsequence. This does
not conflict with the published quadratic-exponent upper bounds; nor does
it by itself establish any optimal counting order.

## 5. The supplementary row-permutation statement

The source also describes the formulation that first forms the block
matrix [A B; A -B] and then arbitrarily permutes its 2m rows. I checked its
claimed fiber size independently.

For a fixed output, its first-half equality classes recover the matching
as above. A preimage in the row-permutation formulation is specified by
ordering the m pairs (m! choices) and selecting which member of each pair
came from the first block (2^m choices). These choices recover A,B and
the row permutation uniquely. Conversely each choice is legal: it gives
a common row permutation of the original A and B followed by independent
row sign changes of B, all of which preserve the Hadamard property.
Thus each output has exactly 2^m m! preimages. This agrees with the source
and introduces no additional assumption into the main injection proof.

## 6. Independent exact checks and their limits

[The independent standard-library checker](independent_check.py) was
written during this audit; the author's checker was not imported or used.
It enumerates Hadamard matrices by exact orthogonality of sign rows, then
constructs and decodes matching-indexed outputs using integer arithmetic.

The saved [output](independent-check.json) records:

- Exact enumeration H(1)=2, H(2)=8, H(4)=768.
- Entire matching-construction domains for m=1 and m=2: respectively
  4 and 192 distinct valid outputs, each decoded to its exact input triple.
- For m=4, all 105 matchings and 16 deterministically selected matrices
  per input factor: 26,880 distinct valid order-eight outputs, with exact
  recovery of every triple. This is an explicitly limited domain, not
  complete enumeration at m=4.
- Entire row-permutation domains for m=1 and m=2: 8 and 1,536 input
  triples, 4 and 192 outputs, and uniform fibers 2 and 8.
- Exact integer comparison of the recursive lower count with the displayed
  bound for k=2,...,12. The code raises to the eighth power to avoid
  floating-point logarithms or nonintegral exponents.

Checker SHA-256:
`32f7075755dd22775d34a9d8568ece5b114d8778057ed2b5bf4fea8657f86b5c`.

These checks are supplementary evidence for transcription and collisions
at finite orders. The universal verdict rests on the inverse construction
and the analytic recurrence, not on extrapolating from the enumerations.
The output also binds the exact source and canonical target hashes.

## Final judgment and limits of the review

**PASS: the exact frozen manuscript proves a complete counterexample to
the labeled Hadamard counting conjecture in canonical FR-12.** There is
no mathematical amendment requested. Original problem IDs, mathematical
target, and source attribution should be retained in any resolution notice.

The manuscript's original paragraph saying that no independent-agent
review has occurred is historical metadata, now superseded by this report;
a publication wrapper can state the completed review accurately while
preserving the user source unchanged. This report does not certify novelty,
public-branch eligibility, human peer review, or formal verification.
Those are separate from the mathematical and source-scope verdict.
