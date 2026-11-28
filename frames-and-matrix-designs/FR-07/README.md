# FR-07 — Zauner's conjecture on maximal complex equiangular tight frames

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Lean verified  
**Last checked:** 2026-11-27

**Rating rationale:** All-dimension SIC existence is a central structured-design barrier connecting frame theory, quantum information and arithmetic geometry.


## Resolution — 2026-11-27

**Solved affirmatively with Lean verification.** Section 9.2 of
[*Stark units for real quadratic fields and reciprocity laws*](https://hexagonmath.org/2610.00186v1)
by Danylo Radchenko and Campbell Wheeler proves the existence assertion
using the ghost-SIC construction of Appleby, Flammia and Kopp. The
preprint discloses AI assistance. Yaoling Yang's
[all-dimension Lean proof](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000040&version=1) was independently
checked by Palomar on 26 November 2026. Māris Ozols also produced an
[earlier independent Lean development](https://github.com/marozols/SIC-existence).
The [verification evidence](#lean-proof-and-verification-evidence)
includes the argument that the formalized overlap condition forces
the stated tight-frame identity.

For every integer $`d\geq2`$, do there exist $`d^2`$ unit vectors $`\phi_1,\ldots,\phi_{d^2}\in\mathbb C^d`$ satisfying

```math
|\phi_i^*\phi_j|^2=\frac1{d+1}\quad(i\ne j),
\qquad
\sum_{i=1}^{d^2}\phi_i\phi_i^*=dI_d?
```

This is existence of an equiangular tight frame with $`d^2`$ vectors in $`\mathbb C^d`$, equivalently a symmetric informationally complete positive operator-valued measure after dividing the rank-one projectors by $`d`$. The statement concerns existence in every dimension. It does not impose additional Weyl–Heisenberg or order-three symmetry.

These frames attain the optimal coherence for $`d^2`$ unit vectors and lead to highly symmetric Gram matrices. Their construction is a concrete structured matrix design and conditioning problem with applications to state reconstruction. The existence theorem applies to every dimension and yields exact overlap and tightness identities.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 24 and its definition of equiangular tight frames. [Paper](https://arxiv.org/html/2603.29571v1).
2. M. Appleby, S. T. Flammia, and G. S. Kopp, *A Constructive Approach to Zauner's Conjecture via the Stark Conjectures*, arXiv:2501.03970v2 (2025). The abstract and main construction distinguish conjectural/conditional arithmetic input from unconditional all-dimension existence. [Paper](https://arxiv.org/abs/2501.03970).
3. S. Joka, *Symmetric Informationally Complete Positive Operator Valued Measure and Zauner conjecture*, arXiv:2601.13475v5. Cited only as an excluded proof claim: withdrawn May 31, 2026, with the author's comment that the proof is incorrect. [Withdrawal record](https://arxiv.org/abs/2601.13475).

## Status check — 2026-09-10

Searched “Zauner conjecture proof 2026”, “SIC POVM all dimensions solved”, and checked the latest versions rather than relying on search snippets. The apparent January 2026 proof claim is withdrawn; its unchanged abstract must not be read as a valid solution. The Appleby–Flammia–Kopp construction does not give an unconditional proof of the statement. No other general resolution was found.

**Audit update (2026-09-10):** Rechecked the Appleby–Flammia–Kopp conditional construction and Joka’s withdrawn v5, and searched for other general proofs. Many individual dimensions have exact constructions, but the all-dimension existence question remains unresolved; the withdrawn claim is not a solution. This is a bounded literature check, not a proof that no solution exists.

## Related partial result — 2026-11-26

Hassan Khodaiemehr's November preprint reduces existence of a SIC in a
given dimension to a condition on the Galois conjugates of the overlap
units of an associated ghost SIC. Section VII identifies the unresolved
arithmetic hypotheses in the reduction. The exact checks in small
dimensions and the conditional implication do not supply the unconditional arithmetic input established in the resolution above. [Preprint, §§VI.4 and VII](https://arxiv.org/html/2611.01524v1).

## Lean proof and verification evidence

**Source and theorem.** The [immutable proof source](https://github.com/Hertaspace/sic-povm-lean/tree/e74571352233162adee70895903d82f8465fd054)
uses Lean `v4.36.0`. The [dependency manifest](https://github.com/Hertaspace/sic-povm-lean/blob/e74571352233162adee70895903d82f8465fd054/lake-manifest.json)
pins Mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
and Naganori Yamaguchi's class field theory library to
`fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565`. The main declaration
`OpenQuantumProblem23.sicPOVMs` in [the solution module](https://github.com/Hertaspace/sic-povm-lean/blob/e74571352233162adee70895903d82f8465fd054/SICLean/Solution.lean)
uses `SICLean.FinalAssembly.zaunerExistence`. For each natural
dimension at least one it gives `Fin (d ^ 2)`-indexed vectors in the complex Euclidean space
$`\mathbb C^d`$, encoded by `EuclideanSpace`. Each vector has norm one, and
for distinct indices the squared modulus of the coordinate inner
product is the real number $`(d+1)^{-1}`$. The
[compared challenge](https://github.com/Hertaspace/sic-povm-lean/blob/e74571352233162adee70895903d82f8465fd054/Challenge.lean) states these definitions and
the same quantifiers. The original FR-07 dimensions start at two.

**Tightness.** Let $`S=\sum_i\phi_i\phi_i^*`$ for the formalized witness.
Then $`\mathop{\mathrm{tr}}\nolimits S=d^2`$ and

```math
\mathop{\mathrm{tr}}\nolimits S^2
=\sum_{i,j}|\phi_i^*\phi_j|^2
=d^2+\frac{d^2(d^2-1)}{d+1}=d^3.
```

Hence $`\|S-dI_d\|_F^2=\mathop{\mathrm{tr}}\nolimits S^2-2d\mathop{\mathrm{tr}}\nolimits S+d^3=0`$.
Thus the same vectors satisfy both displays in the canonical statement.
The trace argument is the catalog's mathematical statement comparison.

**Checks and reproduction.** [Palomar run 45755702568](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45755702568)
verified the pinned revision on 26 November 2026. Its
[mechanical report](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-26-000040-v1/ca365cca899b61b8359b205ff8cff7f600d23ea732e58e377559b773a00f4a43/mechanical-report.json) records successful
build and Comparator checks. The solution and challenge digests in that
report match the pinned files. The [public proof log](https://github.com/Hertaspace/sic-povm-lean/blob/e74571352233162adee70895903d82f8465fd054/VERIFICATION.md)
records successful `lake build`, `lake env lean CheckAxioms.lean`
and `lake comparator --paranoid` on 24–25 November, with the
standard transitive axioms `propext`, `Classical.choice` and
`Quot.sound`. The [automated review](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-26-000040-v1/ca365cca899b61b8359b205ff8cff7f600d23ea732e58e377559b773a00f4a43/review.json)
confirmed the statement and definitions. It records that the proof
summary omits the finite-or-cofinite coordinate-image argument and the
transfer to complex solutions, both present in the checked sources.
The catalog checked the pinned statement, hashes, and public reports
and reran the structural challenge comparison. The public logs supply
the Lean kernel replay.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
