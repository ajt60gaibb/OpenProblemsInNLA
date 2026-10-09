# Independent statement review 1: TR-13

Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Review date: 28 September 2026.

**Verdict: PASS for mathematical statement fidelity.** This is an independent
AI-agent review of the actual files listed below, not human review, endorsement,
or proof verification. The reviewer has not authored the definitions, challenge,
or solution. No solution proof bodies were reviewed. The coordinating agent
subsequently reported that `lake build NLA.TR13.Definitions Challenge` passed
with pinned Lean 4.33.1 and mathlib, with only the expected Challenge placeholder
warning. This reviewer did not independently rerun that build.

## Frozen inputs inspected

Source repository HEAD independently checked as
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.

| File | SHA-256 |
| --- | --- |
| `NLA/TR13/Definitions.lean` | `f026f45877d8e2bfc94a96c8be0dece8a1f2a843d8c1b7249891d720c42240c7` |
| `Challenge.lean` | `03d4522916e4763daf0c06a01393a31372c4eed4a0be48885eae6085598d4c8c` |
| `NUMERICAL_TARGETS.md` | `5e9582f8125ad61ac473312dba9332bdeca5339a9b897570fdd20942deace5ca` |
| `tensor-computations/TR-13/README.md` in source repository | `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f` |
| `references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex` in source repository | `2adb85e04d4d257399049fea3f4e946f6a8d586349bbab411a372de9207f07ea` |

The complete canonical README and complete Colbrook manuscript were read. The
manuscript proves the stronger domain `m >= 3`; restricting the challenge to
the original catalog domain of odd `m >= 5` omits no case of TR-13.

## Semantic checks

1. `Tensor m n = (Fin m -> Fin n) -> Complex` is the complete coordinate
   tensor space with `n^m` complex entries. `hankel h` uses the sum of
   zero-based indices, exactly matching the canonical statement after shifting
   its one-based indices. Its moment array has length `m*(n-1)+1`.

2. `OrdinaryRankAtMost` permits arbitrary pure product summands in all modes.
   Although it has no separate scalar coefficient, a scalar can be absorbed
   into one factor because the theorem assumes `m >= 5`. Zero factors allow
   padding, so an exact list of `q` summands correctly means rank at most `q`.

3. `SymmetricRankAtMost` permits arbitrary complex scalar multiples of
   `v` tensor-powered `m` times. `VandermondeRankAtMost` restricts that same
   construction to exactly the homogeneous rational-normal-curve vector in
   the README and requires `(a,b) != (0,0)`. The `a=0`, `b!=0` point at infinity
   is included. Zero coefficients allow padding with any admissible node.

4. Both border-rank predicates use sequences converging in the finite product
   topology on complex entries, which is entrywise convergence. The ordinary
   sequence terms lie in the entire tensor space, constrained only by ordinary
   rank at most `q`: no Hankel or symmetric restriction is inserted. The
   symmetric sequence terms are likewise full arrays, with symmetry enforced
   by their actual symmetric decompositions. These are the two exact border
   conventions in the canonical problem.

5. The five rank values are the infima of the corresponding sets of natural
   decomposition lengths. For a nonempty set of natural numbers this is its
   least member. An empty natural-number infimum is zero; this is a general
   definitional caveat outside the theorem's successful domain, not a route to
   this theorem: `expectedRank m n >= 3` for `m >= 5`, `n >= 2`, so an empty
   defining set cannot satisfy the asserted equality. The proof should still
   establish nonemptiness of all five sets on the final open set before using
   rank-minimum lemmas, as `NUMERICAL_TARGETS.md` explicitly requires.

6. `expectedRank = (m*(n-1)+2)/2` with natural-number division is exactly
   `ceil((m*(n-1)+1)/2)`. The challenge includes all five ranks with no omitted
   equality, and asks for this stronger exact value instead of merely equality
   among the five ranks. This agrees with the recorded complete solution.

7. `principalOpen p` is exactly `{h | eval h p != 0}` in the complex affine
   moment space. It is a principal Zariski-open set; requiring both `p != 0`
   and explicit nonemptiness prevents a vacuous genericity claim. The moment
   parametrization identifies this affine space with the Hankel tensor space:
   each sum index from `0` through `m*(n-1)` occurs among tensor coordinates.
   Thus this is an adequate, concrete version of the original nonempty
   Zariski-open assertion and introduces no result-assuming hypothesis.

## Proof boundary and remaining obligations

The deliberate `sorry` in `Challenge.lean` is the proposed comparison boundary,
not evidence of a proved result. A valid solution must not import this boundary
or any declaration whose proof depends on it. It must supply a matching theorem
with no `sorry`, unproved axioms, or forbidden native-decision trust, and its
axiom dependencies must be checked separately.

The proof outline in `NUMERICAL_TARGETS.md` is mathematically aligned with the
target, including the full-ambient ordinary-border lower bound and the separate
binary case. This review does not certify that the proposed Prony construction,
Koszul certificate, specialization, or rank comparisons have been implemented
or proved. The eventual proof review must specifically check nonemptiness of
the rank sets, the actual nonempty intersection of upper/lower principal opens,
and continuity of the certificate on arbitrary ambient tensor sequences.

No statement change is requested. The reported typecheck passes the declaration
gate; independent complete proof verification remains required.
