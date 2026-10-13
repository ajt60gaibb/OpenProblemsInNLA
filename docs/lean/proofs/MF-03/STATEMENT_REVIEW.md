# MF-03 pre-proof statement review and feasibility assessment

**Reviewer:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Status:** Source and frozen Lean statement correspondence reviewed; no proof
module implemented or approved by this review. A separate independent
statement review is required before proof implementation.

## Selection from the 37 statement-only Solved targets

MF-03 is the most bounded **standalone** full target I found after excluding
FR-05, TR-13, RA-06 and MF-23. Its source proof is a focused 214-line
one-variable argument, with exact rational certificates for the only 15
orders left by its all-order estimate. The target has no probability,
finite-machine or generic-algebraic-geometry semantics. This makes it a
better next research project than MD-04 (a short corollary, but only after
formalizing the deep unproved MD-03 Komlós input), PF-05 (depends on a
separate positive-entry rigidity theorem), SP-11/SP-12 (Hall's all-graph
delta theorem), or TR-14 (the 906-line apolarity proof for every exceptional
Hankel tensor).

**Feasibility limit:** a complete MF-03 Lean proof is **not modest** in the
usual implementation sense. Mathlib has power-series and polynomial
infrastructure, but a targeted search of the pinned checkout found no
Jacobi–Trudi, semistandard-tableau, Schur-function or Padé-approximant theorem
that supplies the manuscript's central denominator formula. The cosine
infinite product and its coefficient bridge also need formal work. The
finite 15-order part is bounded and certifiable, but completing the all-order
step is a substantial new development. No external theorem may be declared
as an axiom or silently assumed. If a genuinely modest complete target is
required, this inventory does not establish one among the remaining 37.

## Exact canonical and frozen target

The permanent registry maps `MF-03` to
`matrix-functions-and-stability/MF-03/README.md`. The canonical question is
about the diagonal `[m/m]` Padé approximant at zero to the **entire** function

```text
f(z) = Σ_{j≥0} z^j/(2j)! = cosh(√z),
```

where the series removes any square-root branch choice. For **every**
integer `m≥1`, the reduced rational approximant must have no pole on the
**closed complex disk** `|z|≤3`, and satisfy `|1−r_m(z)|≤2` there.

The live `NLA.Statements.MF03.Target` and frozen
`NLA.ReviewedStatements.MF03.Target` express this as follows:

1. `NormalizedPadeRepresentation m P Q` requires complex polynomials of
   `natDegree≤m`, `Q.eval 0=1`, and the exact coefficient identity
   `Σ_{i=0}^j Q.coeff i / (2(j−i))! = P.coeff j` for **each** `0≤j≤2m`.
   These are exactly the coefficients through degree `2m` of `Q f − P`
   vanishing; the source error term is `O(z^(2m+1))`. The constant term
   forces `P.coeff 0=1`, so the zero-polynomial `natDegree` convention does
   not weaken the actual witnesses.
2. `ReducedPadeRepresentation` additionally requires `IsCoprime P Q`.
   This matches cancellation of removable common factors before testing
   poles. The proof must show a reduced normalized pair **exists**; the
   separate existence conjunct in `Target` prevents a vacuous universal
   bound. Cancellation is legitimate because `Q(0)=1`; normalized Padé
   identities and the degree bound imply the rational quotient is unique.
   These are proof obligations, not assumptions supplied by the definition.
3. The universal conjunct ranges over **every** reduced normalized pair
   and every complex `z` with `‖z‖≤3`. It demands both `Q.eval z≠0` and
   `‖1−P.eval z/Q.eval z‖≤2`. Complex norm is modulus, and
   `|1−r|=|r−1|`. Neither a smaller disk, a real-axis bound, a bound for
   selected orders, nor a strict replacement for the weak `≤2` is used.
   The source proves the stronger strict inequality for `m≥2`, but `m=1`
   reaches equality, so the weak boundary is essential.

The source theorem includes `m=0` and a matrix spectral-radius corollary;
neither is part of the retained canonical scalar target. Conversely, the
Lean target's explicit reduced-pair existence and `∀ P Q` wording are
faithful to the canonical single-rational-function statement once uniqueness
and reduction are proved. I found no mathematical or numerical weakening in
the frozen target. The live and frozen definitions are textually the same
apart from namespace and header comments.

## Source resolution and exact numerical checkpoints

The reviewed resolution is Theorem 1 of the preserved MF-03 manuscript,
with the independent source audit listed below. Its all-order argument gives
the denominator coefficient bound `0<b_(m,j)≤S_m^j`, where
`S_m=Σ_{ν>m} 1/[π²(ν−1/2)²] < 1/(9m)`. The disk lemma uses `R=3` and
`2 R S_m<1`, obtains `Q_m(z)≠0`, and bounds

```text
|1−P_m(z)/Q_m(z)| ≤ (f(3)−1)/(1−6 S_m).
```

The rational estimate is `f(3)≤6179/2120<35/12`. For `m≥16`,
`6 S_m<1/24`, hence the displayed bound is **strictly** below
`(23/12)/(23/24)=2`. The finite certificate covers **every** `m=1,…,15`.
For each order it lists exact rational coefficients and checks the full
Padé identities through `2m`, plus

```text
B_m = Σ_{j=0}^m |q_(m,j)| 3^j < 2,
N_m = Σ_{j=0}^m |p_(m,j)−q_(m,j)| 3^j ≤ 2(2−B_m).
```

The reverse triangle inequality then gives denominator nonvanishing and
the required bound throughout the closed disk, rather than just at sampled
points. At `m=1`, `P=1+5z/12`, `Q=1−z/12`; at `z=3`, `P/Q=3` and the
error is exactly `2`. The original Nadukandi–Higham lemma covered orders
`1,…,20`; the new proof uses finite certificates only through 15 because
the analytic estimate starts at 16. There is no gap between the ranges.

I reran the preserved standard-library Python certificate verifier with
`--verify`: it exited zero and reported all 15 finite Padé certificates and
the rational `f(3)` bound PASS. This is source evidence, **not** a Lean
kernel proof. A Lean implementation should check compact rational witnesses
and these two aggregate inequalities in the kernel, avoiding exhaustive
complex-disk computation. The all-order denominator theorem and analytic
series bounds must still be proved, not imported as a source claim.

## Lean boundary check and next proof obligations

With the pinned Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran
`lake build NLA.Statements.MF03 Reviewed.MF03`; it exited zero (1874
jobs). The statement modules' LeanCert `#assert_statement` and
`#assert_trust kernel` directives passed and `#print axioms Target` listed
only `[propext, Classical.choice, Quot.sound]`. **This checks definition
trust, not the truth of `Target`.** No theorem proving `Target` exists yet.

A credible full proof needs: (i) exact Padé existence/uniqueness and
coprimeness for every `m≥1`; (ii) the all-order coefficient/tail bound,
including the cosine product or an independently proved equivalent route;
(iii) the analytic disk estimate and the strict rational arithmetic for
`m≥16`; (iv) kernel-checked rational witnesses and aggregate inequalities
for `1≤m≤15`; and (v) transport of the result to **every** reduced pair in
the frozen proposition. The final exported theorem must have the literal
frozen `Target` type and pass LeanCert in kernel mode and Comparator review.

## SHA-256 of reviewed inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/results/wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `references/colbrook-matrix-functions-2026-09-11/code/wave_kernel_certificate.py` | `73587f8a4a5afd12bd6f33ae9ffb5b85c9388831cf152b48a4c64595f84c3155` |
| `references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-03-review.md` | `cccbb11ca9e42a0f27e72d3b351f76c66b5a06eee69f7c6e367ebab8e0c79423` |
| `docs/lean/statements/MF-03/NUMERICAL_TARGETS.md` | `7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/Reviewed/MF03.lean` | `a0c55c3f315c5330d8da170fc2f4c8ac6dab715b8a30b0111660d262ea0d0674` |
