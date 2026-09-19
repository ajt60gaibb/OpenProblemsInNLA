# NR-04: numerical statements and full-target boundary

Status: proposed statements only. Written before the new Lean definitions and
reference headers. No Lean compilation, proof implementation, Comparator run,
independent statement approval, or completed formalization is claimed here.

The unchanged canonical question asks whether the real nonnegative matrix
`D_ij = (i-j)^2`, for `1 <= i,j <= 9`, admits a real nonnegative factorization
of inner dimension six. Matthew J. Colbrook's complete retained manuscript
proves its nonnegative rank is seven. The formalization contribution is by
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, with OpenAI Codex assistance. This is not
a claim of new mathematical authorship.

## Exact data and indexing

Lean uses `Fin 9`, so `D i j = ((i.val : Real) - (j.val : Real))^2`.
Adding one to both indices leaves every difference unchanged. All proposed
factor variables have entries in `Real`, without rationality, algebraicity,
symmetry, genericity, stochasticity, or rank restrictions in the final claim.

Put `t_i = i.val - 4`, and `a_i = |i.val - 4|`, with the latter first taken
in the integers and then regarded as a natural number. Thus `0 <= a_i <= 4`
and the real coercion of `a_i` is exactly `|t_i|`. Define seven columns/rows
by the source's formula, now with factor indices `r = 0,...,6`:

- For `r < 5`, `W i r = 1` when `a_i = r`, and zero otherwise;
  `H r j = (r-a_j)^2`.
- `W i 5 = 2 max(t_i,0)` and `H 5 j = 2 max(-t_j,0)`.
- `W i 6 = 2 max(-t_i,0)` and `H 6 j = 2 max(t_j,0)`.

The entire product is reduced symbolically to the universal real identity

`(|s|-|t|)^2 + 4 max(s,0) max(-t,0) + 4 max(-s,0) max(t,0) = (s-t)^2`.

No decimal input, approximate factorization, or search over real factors is
permitted. The upper witness uses exact integers through real coercions.
Checking this upper witness alone does not prove the canonical lower bound.

## Minimized numerical obligation

The leading three-by-three minor is exactly
`[[0,1,4],[1,0,1],[4,1,0]]`, with determinant `8`. The only proposed
LeanCert inequality is `0 < (8 : Real)`, consumed to prove this minor is
nonzero and hence that the full matrix has rank at least three. Use the
pinned LeanCert in kernel mode. There are no interval variables and no
subdivision; the exact determinant reduction is symbolic. This intentionally
small certificate satisfies the required kernel-mode numerical workflow
without turning 81 matrix entries or unbounded real factor variables into
interval computations. A direct exact rank-at-most-three factorization
uses `(s-t)^2 = s^2 + t^2 - 2*s*t`.

## Proposed reference contracts

These are obligations to prove, never oracle premises in the final theorem.
The exact names and quantifiers are written in the independent `Challenge.lean`.

| ID | Declaration | Full assertion and source role |
| --- | --- | --- |
| C01 | `minor_eight_positive` | `0 < (8 : Real)`; kernel-mode LeanCert boundary, consumed in C06. |
| C02 | `distance_index_semantics` | Every zero-based matrix entry equals the canonical one-based formula. |
| C03 | `centered_labels` | Every exact natural label is at most four and coerces to the absolute centered coordinate. Includes center zero and both endpoints. |
| C04 | `reflection_identity` | The displayed scalar identity for all real `s,t`, including zeros and equal or opposite signs. |
| C05 | `seven_factor_certificate` | The actual nine-by-seven and seven-by-nine witness matrices are entrywise nonnegative and multiply exactly to `D`. |
| C06 | `distance_rank_certificate` | The specified leading minor has determinant eight, and the ordinary real rank of `D` equals three. |
| C07 | `distance_sign_pattern` | The actual matrix is entrywise nonnegative, has zero diagonal, and every off-diagonal entry is strictly positive. |
| C08 | `small_section_bound` | For normalized nonnegative columns `U` with at most six generators and rank at most four, and normalized rank-three columns `X` in their convex hull, the section of `conv(U)` by `aff(X)` has finitely many actual extreme points and at most eight. |
| C09 | `section_contact_bound` | For normalized rank-three columns `X` with exactly one diagonal zero and strictly positive off-diagonal entries, inside the convex hull of arbitrary finitely many normalized nonnegative columns `U`, the same actual section has finitely many extreme points and at least `N` of them. |
| C10 | `low_rank_factor_obstruction` | A real nonnegative factorization `M=W*H` of width at most six, `rank M=3`, zero diagonal, positive off-diagonal, and `rank W<=4` implies `N<=8`. The proof must perform legitimate normalization, including removing zero columns, rather than assume it for arbitrary factors. |
| C11 | `rank_three_small_factor` | For arbitrary real factors with inner dimension at most six and product rank three, at least one factor has rank at most four; derive this from actual rank-nullity/Sylvester theory. |
| C12 | `general_rank_seven_lower` | Every real rank-three square matrix of order at least nine with that sign pattern has no nonnegative factorization of any width `k<=6`. Includes nonsymmetric matrices and all smaller widths. |
| C13 | `nine_point_no_small_factor` | Specialize C12 to the actual distance matrix, for every natural width at most six, including zero. |
| C14 | `nine_point_nonnegative_rank_seven` | Seven is the least natural inner dimension admitting a real nonnegative factorization of the actual matrix. Expressed using Mathlib `IsLeast`, so existence and the lower bound are both present without a default value for a nonexistent minimum. |
| C15 | `canonical_six_factor_impossible` | No real nonnegative `W : Matrix (Fin 9) (Fin 6) Real` and `H : Matrix (Fin 6) (Fin 9) Real` satisfy `W*H=D`. This is the original question's explicit negative answer. |

## Geometry that must be proved internally

C08 is the manuscript's two-/three-dimensional section argument. Normalized
columns lie in the affine hyperplane whose coordinate sum is one; its affine
dimension is ordinary column rank minus one. Rank three of `X` forces a
two-dimensional section. In affine dimension two there are at most six
vertices. In affine dimension three a polytope with `v<=6` vertices has at
most `2*v-4<=8` facets, by Euler and the planar graph bound, and a plane
section described by those facets has at most eight edges and vertices.
Repeated generators, nonextreme generators, nonsimplicial facets, and planes
through a vertex, edge, or facet are included. The final theorem may not
take the Euler/facet bound or general position as an assumption.

C09 is the applied polygon-contact lemma. With `L=aff(X)`, the outer polygon
is `P = L intersect {x | forall i, 0<=x_i}`. Every column `X_:j` lies in
the relative interior of the distinct edge cut out by coordinate `j=0`.
The inner section contains every such contact. The source's half-open
normal-cone assignment handles support directions exposing an edge instead
of a unique vertex. That degeneracy must survive the formal proof.

The current bounded pinned-Mathlib search located convex hulls, actual
extreme points, exposed sets, affine dimensions, matrix rank and rank-nullity.
It did not locate the necessary three-dimensional polytope Euler/facet
bound or a ready-made polygon-contact lemma. This is a substantial remaining
implementation cost; a short written proof is not evidence of a short Lean
proof. The source packet is worthwhile as a faithful next-target boundary,
but no completion estimate is attached.

## Statement gate and verification policy

Before substantive proof code, two independent nonauthor reviewers must read
the full canonical source, full retained proof, this plan, transparent
definitions, and all fifteen exact headers, recording their input hashes.
They should challenge the quantifiers, cardinalities, normalization, sign
pattern, section degeneracies, and minimum semantics. Header elaboration is
a separate mechanical check and is not a proof. Any amendment changes hashes
and requires an explicitly scoped review continuation.

Only after those approvals should one serial local Lean process compile the
proofs with one thread and the campaign's 4096 MiB bound. `Solution` must
never import `Challenge`. All fifteen exports must ultimately pass the real
non-root Linux Comparator, its kernel and allowed-axiom checks, with
`definition_names=[]` and only `propext`, `Classical.choice`, `Quot.sound`
permitted. Neither local Lean nor Comparator has run for this new packet.
No new resolved or verified target is counted by preparing these statements.
