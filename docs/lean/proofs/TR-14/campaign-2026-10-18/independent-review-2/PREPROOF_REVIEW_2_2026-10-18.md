# TR-14 independent exact-statement and whole-target route review 2

Reviewer: OpenAI Codex AI agent `/root/fr05_statement`, 18 October 2026.
**APPROVE the unchanged full statement and the explicit remaining proof route
below before new implementation. No mathematical statement blocker found.**
This review was written independently of the other new review; I have not read
that agent's new findings. It is not a proof of Target, implementation approval
of all existing modules, or a Linux/Comparator acceptance claim.

## Inputs and immutable scope

I read the canonical README/problem TeX, exact numerical specification, live
and separately frozen Lean boundary, the essential complete source argument
in `solution.tex` Sections 1–5, the terminal-sequence appendix, and the actual
later candidate at commit `fdb40b66425ec58e4806cee93d2aaf92a0f8597c`.
The candidate checkout was clean and was accessed read-only. Its 39 proof
modules contain 4,536 lines. Public conclusions and their dependencies were
inspected to distinguish proved support from the unimplemented full gates.
No current SP-12 package or other chat worktree was edited.

[`input-lock.json`](input-lock.json) records exact hashes for the original
artifacts, source manuscript, specification, live/frozen statements, existing
contracts and every one of the 39 candidate modules. Important hashes are:

| Input | SHA-256 |
| --- | --- |
| Canonical README and retained ORIGINAL | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Actual attributed solution TeX | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Live statement | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Frozen Reviewed.TR14 | `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356` |

Some historical route contracts print an abbreviated/incorrect solution hash;
this review uses the freshly computed full actual hash above. The reviewed
canonical originals and statement bytes also match the active campaign clone.
The append-only registry still maps TR-14 to
`tensor-computations/TR-14/README.md`; its ID, path and mathematical target are
preserved.

## Exact theorem approved

The required public declaration remains `target : NLA.Statements.TR14.Target`:
for **every** natural `m,n` with `3 ≤ m`, `2 ≤ n`, every
`h : Fin (m*(n-1)+1) → ℂ`, and **every** natural width `R`,

```lean
OrdinaryWidth (Hankel h) R ↔ SymmetricWidth (Hankel h) R
```

`HankelIndex` sums zero-based `Fin n` values; this is precisely the canonical
one-based index sum minus `m`. Ordinary summands have fully independent
summand/mode factors `u j k`; symmetric summands use one vector `v j` and a
complex scalar `c j`. Multiplication is complex bilinear, with no conjugation.
Neither factors nor weights are required nonzero. Width zero is an empty sum.
The tensor may be zero, exceptional, balanced, mixed-multiplicity or have a
chosen apolar root at infinity in the original chart. There is no generic,
Vandermonde-only, binary-dimension-only, nonzero, border-rank or prescribed-rank
restriction. Binary *apolar forms* are an internal tool for all dimensions
`n≥2`, not a restriction to `n=2`.

The all-width equivalence faithfully expresses equality of minimum exact
ranks. Zero padding makes each width predicate upward closed. A symmetric
summand becomes ordinary by absorbing its scalar into one existing mode.
Conversely, a matching symmetric witness at a proved lower bound can be padded
to the given ordinary width. For the hard direction, the given ordinary
witness itself supplies nonemptiness when selecting a least ordinary width;
no total-rank default on an empty set is needed. Zero is handled separately.
Existing WidthBasics and WidthPadding already prove the elementary reverse,
zero-width and monotonicity facts. A final all-width assembly is still absent.

I freshly compiled copied Infrastructure, live TR14 and frozen Reviewed.TR14
in an isolated output directory with pinned Lean 4.33.1/Mathlib/LeanCert imports.
All three passed. The two boundaries print only `propext`, `Classical.choice`,
`Quot.sound`; their text is identical after the reviewed namespace/header change.
Raw commands/log hashes are in [`boundary-build.json`](boundary-build.json).
This checks the exact boundary, not the 39-module proof implementation.

## What the 39-module candidate actually supplies

The least nonzero homogeneous apolar degree `r₀` exists and satisfies
`1≤r₀≤D/2+1`, where `D=m(n-1)`. The chart modules construct an actual invertible
mode change, transport apolarity and both widths, and normalize a chosen
minimal form to a monic affine polynomial `g` of exact degree `r₀`. Moment
quotient and Frobenius modules match every moment through `D` and prove the
actual nondegenerate pairing. Middle-catalecticant support identifies the rank.
The local CRT modules retain whole repeated-root factors, construct the
functional's local unit roots and exact Fourier sums, count their nodes, and
produce an actual symmetric width

```text
L = (m−1)r₀ − (m−2)s,   s = card(localRootSupport g).
```

ChartLocalFourierWidth transports that witness back to original `h`, under
minimal-apolar hypotheses that the existing existence/normalization modules
can supply. This is a genuine local symmetric upper bound, not Target.

The five later modules relative to the earlier 34-module campaign copy are
WidthPadding, BinaryFrobeniusRepresenter, BinaryTopRemainder,
BinaryTopRemainderFrobenius and BinaryMomentUnitInverse. They add padding and
prove the actual top-remainder pairing, unique Frobenius representer and
inverse-unit existence. They do **not** construct the binary upper witness,
an unrestricted ordinary lower bound, or the final all-width theorem. No
candidate theorem with conclusion Target or either missing lower/upper gate
was found. Existing informal reviews do not replace those Lean obligations.

## Remaining binary symmetric upper bound: exact approved route

Set `v=D−r₀+2`; least degree implies `v≥r₀>0` and `v≤D+1`.
BinaryMomentUnitInverse supplies a unit inverse class. Its unique representative
`b` has degree `<r₀`, is coprime to `g`, and obeys the required low moment
annihilation equations. The last two facts still need actual Lean proofs.
They must be derived from the proved inverse equation and all-moment pairing.

A concrete affine pencil avoids adding projective or rational-function APIs:
choose `a` outside the finite zero set of `b`, put
`A=g*(X−C a)^(v−r₀)`, and use `b+c*A` with `c≠0`. Then A is monic of degree v,
`b` is coprime to A, and `deg b<v`. The Wronskian `b'*A−b*A'` is nonzero in
characteristic zero: its leading coefficient is the nonzero leading coefficient
of b times `deg b−v` (with the constant-b case included). Every repeated finite
root of the pencil forces a root of this fixed nonzero Wronskian. Coprimality
ensures A does not vanish there. Exclude the finitely many resulting values
`c=−b(β)/A(β)` and zero. Dividing by c makes the selected polynomial monic,
without changing degree, roots or the homogeneous linear moment recurrence.
The degree-v recurrence follows from apolarity of b and multiples of g.
Balanced `v=r₀` uses exponent zero and is included.

The proposed separate reconstruction theorem is **approved**: for the actual
D and moments, a monic squarefree P of degree `v>0`, `v≤D+1`, and the actual
recurrence for every `ℓ` with `ℓ+v≤D` imply
`SymmetricWidth (Hankel h) v`. Complex splitting supplies exactly v distinct
finite roots; the invertible v-by-v Vandermonde system matches the first v
moments, and monicity propagates to every remaining moment through D. Vectors
`β_j^i` then satisfy the frozen tensor coordinate equation exactly.

The recurrence must retain `ℓ+v≤D`, rather than an unguarded range ending in
natural `D−v`. This includes `r₀=1`, `v=D+1`: the recurrence is genuinely empty,
and the first-v system already matches all moments. Thus this route can cover
that endpoint uniformly; a separate rank-one construction and padding is also
valid if proved. No unavailable `IsApolar` value at degree `D+1` may be assumed.
The practical first new proof gate is inverse representative → coprimality and
bounded moment annihilation, then the finite-bad-pencil-value theorem. The
reconstruction theorem is independent parallel work once both reviews approve.

## Remaining arbitrary ordinary lower bound: indispensable full gate

For any nonzero normalized moments, the required theorem is

```text
OrdinaryWidth (Hankel h) R → min(v,L) ≤ R.
```

The supplied source's Sections 4–5 give a coherent route, but this is a large
new finite-algebra development. No candidate module proves it. A minimum
ordinary decomposition must retain arbitrary mode-dependent factors; minimality
proves its decomposable terms linearly independent. Form graph subspaces in
`B=AdjoinRoot(g) × ℂ^R`, choose actual units by avoiding finitely many proper
hyperplanes, and normalize the graph spaces to contain 1. The actual ordinary
decomposition proves Frobenius annihilation. Independence proves surjectivity
onto the coordinate ℂ^R factor. Every all-but-one mode product must surject onto
the moment algebra; the source degree bound `(m−1)(n−1)≥r₀−1` proves this.

Next prove the transformation lemma and its contextual product inequality.
The ordinary Kneser inequality may not be assumed in the ambient nonreduced
algebra. The annihilating Frobenius functional excludes nilpotents from **each**
auxiliary algebra. Only then may reduced subalgebras be classified by partitions
of the finite set of whole local factors and a common auxiliary algebra selected
along a Vandermonde basis of units. The final stabilizer is likewise reduced.
Primitive blocks must retain whole repeated-root local factors and have
nonempty moment-algebra support. The exact block inequality is

```text
R_j ≥ m*min(n,r_j) − r_j − m + 2.
```

If any `r_j≥n`, it gives `R≥v`; if all `r_j<n`, summing gives `R≥L` using
`t≤s`. These inclusive alternatives give precisely the minimum. Replacing this
with L alone is false: the source example `m=5,n=3,r₀=4,s=2` has L=10 and v=8.
A flattening rank `r₀`, a single-support substitution bound, an algebra rank
bound restricted to a mode subspace, or a symmetric/Vandermonde-only lower
bound cannot replace this arbitrary-decomposition gate.

I also checked the cited [Beck–Lecouvey primary paper, Lemma 4.2](https://cml.centre-mersenne.org/item/10.5802/cml.34.pdf),
printed pp. 15–16: its transformation argument is the source's finite-dimensional
commutative specialization. The full Kneser theorem there has additional
finiteness hypotheses. The contextual nilpotent-exclusion argument must therefore
be proved, not imported by dropping those hypotheses. Credit to Beck and
Lecouvey remains necessary. The primary browser/PDF reading is identified by
URL and date; no uncomputed raw PDF hash is claimed.

## Whole-target closure, feasibility and limits

Choose one normalized minimal g, prove both symmetric upper witnesses and the
ordinary lower minimum for that same g, and select the smaller witness. Pad
to every supplied ordinary width; use the existing reverse and zero facts.
Finally transport widths back to the original h. The target contains no root
invariant, so a global original-projective-root multiplicity correspondence is
**not required** if the finite support count of the one normalized g is used
consistently throughout. Exporting the stronger original-coordinate formula
would require that additional correspondence: the existing nonzero-affine-root
bijection explicitly leaves infinity and multiplicity gates separate.

The binary branch has concrete polynomial, root and Vandermonde APIs in pinned
Mathlib and is a feasible next implementation. The lower branch is the main
risk and requires genuinely new subspace-product/stabilizer/partition proofs;
it is not a routine final wrapper. Both must be completed without new axioms,
admissions, assumed classification, weakened widths or altered originals.
A future full target needs independent implemented-source review, kernel/axiom
checks, a self-contained canonical boundary with fresh approvals, and actual
isolated Linux Comparator evidence. TR-14 remains Solved with partial Lean
support until all gates are actually discharged.
