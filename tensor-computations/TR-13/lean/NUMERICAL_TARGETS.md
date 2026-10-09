# TR-13: frozen full target

Source repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
Problem/conjecture credit: Jiawang Nie and Ke Ye. Mathematical resolution:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge. Formalization development: OpenAI Codex agents;
no claim of human review or endorsement.

## Source SHA-256

- `tensor-computations/TR-13/README.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-13.tex`: `2adb85e04d4d257399049fea3f4e946f6a8d586349bbab411a372de9207f07ea`

## Domains and conventions

Every odd integer m ≥ 5 and every integer n ≥ 2 is included. The scalar field
is ℂ throughout. A tensor is its full array of n^m complex entries, indexed
by `Fin m → Fin n`. The parameter space is ℂ^(D+1), D=m(n−1).
The Hankel entry at i is h_(Σ_j i_j), with zero-based indices.

Ordinary rank allows arbitrary complex pure product summands. Symmetric rank
allows complex scalar multiples of v^⊗m. Vandermonde rank restricts v to
(a^(n−1), a^(n−2)b, …, b^(n−1)) with (a,b)≠(0,0), including a=0.
Zero coefficients permit padding all decompositions to the stated length.
Ranks are the least nonnegative lengths. The proof must show all five defining
sets nonempty on the advertised open set, so the empty-set sInf convention
cannot manufacture a rank assertion.

Border rank uses sequences of arbitrary full arrays having rank at most q,
converging in the finite product topology on complex entries. Symmetric border
rank uses symmetric rank at most q at each term. There is no Hankel or symmetry
restriction on the ordinary border sequence. No probability law, norm bound,
precision model, or computational complexity assertion is part of the target.

## Complete theorem

`NLA.TR13.generic_rank_equality` asserts the existence of a nonzero multivariate
polynomial p and a point where p evaluates nonzero. For every h with p(h)≠0,
all five original ranks equal r=(D+2)/2 using integer division, i.e.
ceil((D+1)/2). This is stronger than the original equality-only question.
The set `{h | p(h)≠0}` is a principal Zariski-open subset of the affine moment
space, and the separately required point makes nonemptiness explicit.
Definitions use no parameter-dependent hypothesis that assumes the result.

## Planned proof and bridges

Upper bound: a Prony recurrence determined by an r×r Hankel matrix and a
nonzero polynomial resultant gives r distinct complex nodes and weights.
Prove the recurrence reconstruction, then the actual Vandermonde decomposition.
This replaces the manuscript's dominance/constructibility argument by algebra.
When D=2r−2 extend by one zero moment, when D=2r−1 retain all moments.

Lower bound: for m=2k+1, put a=k(n−1)+1 and s=floor((n−1)/2), so r=a+s.
For n≥3, the three-slice Koszul matrix must have rank at most twice any
ordinary decomposition length. The two-spike generator at a−1 and 2a+s−1
must supply rank at least 2r and hence a nonzero polynomial determinant
certificate. Continuity of that certificate excludes every sequence of ordinary
rank less than r, in the full ambient space. The n=2 case uses ordinary
flattening and an a×a reversal submatrix instead. Intersect the upper and lower
principal open sets and prove their intersection nonempty. Rank comparison
and constant sequences then yield all five equalities.

## Verification scope

This file specifies the intended complete proof; it is not a verification claim.
Only the comparison boundary may contain a deliberate placeholder. No solution
may import Challenge or use sorry, unproved axioms, or native decision trust.
