# TR-13 independent statement review 2

Date: 2026-09-28.
Phase: pre-proof statement fidelity and scope.
Reviewer: OpenAI Codex agent `/root/environment` (AI agent).
Independence: this reviewer did not implement the definitions or Challenge and
has not implemented any proof in this project. This is an agent review, not
human peer review or source-author endorsement.

## Reviewed sources and exact bytes

Canonical source revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
The two source hashes below agree with `NUMERICAL_TARGETS.md` and with the files
read from the repository at that revision.

| File | SHA-256 |
| --- | --- |
| `tensor-computations/TR-13/README.md` | `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f` |
| `references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex` | `2adb85e04d4d257399049fea3f4e946f6a8d586349bbab411a372de9207f07ea` |
| `NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `Challenge.lean` | `03d4522916e4763daf0c06a01393a31372c4eed4a0be48885eae6085598d4c8c` |
| `NUMERICAL_TARGETS.md` | `5e9582f8125ad61ac473312dba9332bdeca5339a9b897570fdd20942deace5ca` |

I read the full canonical README, full manuscript, and all three boundary files.
I also inspected relevant imported Mathlib definitions and lemmas, including
`Mathlib/Order/Lattice/Nat.lean` (`Nat.sInf_empty`),
`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
(`isLeast_csInf`, `csInf_mem`), and the existing finite-product topology and
polynomial conventions. Mathlib is pinned by the project to
`0df444a360eaa60ab8c11dca51a86af692955474`.

## Findings

1. **Full quantifiers and value are preserved.** The Challenge covers every odd
   natural number `m >= 5` and every `n >= 2`, exactly as the original retained
   question requires. Restricting the manuscript's stronger `m >= 3` theorem to
   `m >= 5` drops only the already-known cubic case, not part of the target.
   `(m * (n - 1) + 2) / 2` is the natural-number expression for
   `ceil((m * (n - 1) + 1) / 2)`. The theorem asserts all five ranks have this
   value, which implies the original equality-only assertion.

2. **The tensor definitions retain all factors.** `Tensor m n` is the full
   coordinate array indexed by functions `Fin m -> Fin n`; `pureTensor`
   multiplies one independently chosen vector entry for every factor. No
   symmetry or Hankel constraint is imposed on ordinary summands. For `m >= 5`,
   scalar multiples can be absorbed in one factor, and a zero vector in one
   factor permits zero summands. Thus the length-`q` representation is the usual
   rank-at-most-`q` condition. Symmetric summands have an independent complex
   coefficient and one vector repeated in every factor.

3. **Projective Vandermonde summands include infinity.** The coordinates are
   `a^(n-1-i) * b^i`, with the pair `(a,b)` explicitly nonzero. Because
   `i < n`, the natural subtraction is the intended exponent. With `a=0` and
   `b != 0`, only the last coordinate survives, including the `0^0=1`
   endpoint. Zero coefficients permit padding without admitting the forbidden
   projective pair `(0,0)`.

4. **The border-rank ambient space is correct.** Ordinary border sequences
   range over `Nat -> Tensor m n`. Their terms are required only to have
   ordinary rank at most `q`. They need not be Hankel or symmetric. Symmetric
   border sequences require symmetric decompositions term by term. The
   standard finite function-space topology over complex numbers is precisely
   coordinatewise convergence. There is no boundedness condition on factors,
   coefficients, or approximating sequences.

5. **The `sInf` convention does not make the target vacuous.** These ranks use
   `sInf` of subsets of the natural numbers. Mathlib assigns zero to the empty
   set, so the definitions are not suitable as unrestricted natural-valued
   ranks of arbitrary arrays lacking structured decompositions. On the
   advertised domain, however, the expected value is at least three. Hence an
   equality to that value cannot be obtained from an empty defining set.
   `NUMERICAL_TARGETS.md` additionally requires actual nonempty decomposition
   sets on the open set. The implementation should establish them from its
   Vandermonde upper bound and constant sequences before using minimum-rank
   comparison lemmas. This is a proof obligation, not a defect in this
   positive-rank Challenge statement.

6. **The genericity assertion is substantive.** `principalOpen p` is exactly
   the nonvanishing locus of a multivariate polynomial over the full moment
   space. The Challenge requires both a nonzero polynomial and an actual
   point of that locus. It then quantifies over every point of the locus;
   neither membership nor the polynomial definition assumes rank equality.
   This is a principal Zariski-open set, a valid stronger form of the original
   existential-open assertion. The moment parameterization has the intended
   `D+1` coordinates: every sum from zero to `m(n-1)` occurs among the tensor
   indices, so the Hankel coordinate map identifies this affine space with
   the Hankel tensor space. No exceptional parameters beyond a genuine
   polynomial zero locus may be discarded by the eventual proof.

7. **The proof plan is distinct from the statement.** The proposed Prony
   argument replaces the manuscript's dominance argument without changing
   the Challenge. Its zero-moment extension in the `D=2r-2` case still needs a
   nonempty upper-bound polynomial certificate; that cannot be assumed. The
   lower-bound plan must work for arbitrary ordinary decompositions and their
   full-ambient limits, as required by the definitions. Neither ingredient
   has been accepted as proved by this review.

## Verdict and limits

**APPROVE the mathematical fidelity and complete scope of the reviewed
statement bytes.** No boundary correction is requested.

This approval is specific to the hashes above. It is not a proof correctness
approval and does not authorize any claim that TR-13 has been Lean verified.
Before finalizing this report I rechecked all three boundary hashes and
inspected `verification/statement-build.log` (SHA-256
`4ffdefe09e3444f4a43a5033c7543166820581924b7965121e63028067d0335d`).
It records a successful build with only the expected Challenge `sorry`
warning. The author identifies the command as
`lake build NLA.TR13.Definitions Challenge` under the pinned toolchain and
Mathlib revision; I inspected the retained output, but did not independently
rerun that command. The deliberate `sorry` in `Challenge.lean` is acceptable only
in that trusted comparison environment; the Solution must not import it.
Any mathematical boundary change reopens this review.
