# MF-03 independent pre-proof statement review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026.
**Verdict:** **approve the exact statement for proof work**, at the source
hashes below. This approves the mathematical and numerical target boundary;
it does not certify a proof of `Target`, the manuscript, or its finite
certificate in Lean. I did not edit the frozen statement or proof source.

## Canonical target and actual Lean proposition

The permanent registry assigns `MF-03` to
`matrix-functions-and-stability/MF-03/README.md`; its preserved `ORIGINAL.md`
has the same SHA-256. The canonical question uses the entire Taylor series
`f(z)=Σ_{j≥0} z^j/(2j)! = cosh(√z)` at zero, with no square-root branch,
and the diagonal `[m/m]` Padé approximant for **every** integer `m≥1`.
It asks that the **reduced rational function** have no pole anywhere on the
**closed complex disk** `|z|≤3`, and satisfy `|1−r_m(z)|≤2` throughout it.

I checked every clause of the live and frozen `Target` definitions:

- `NormalizedPadeRepresentation m P Q` uses genuine complex polynomials,
  `P.natDegree≤m`, `Q.natDegree≤m`, and `Q.eval 0=1`. For each natural
  `j≤2*m`, `Finset.range (j+1)` includes exactly `i=0,…,j`, and the
  coefficient equation is
  `Σ_i Q.coeff i / ((2*(j−i)).factorial : ℂ)=P.coeff j`. This is exactly
  vanishing of every coefficient of `Qf−P` through `2m`, equivalent to the
  source's `O(z^(2m+1))` condition. The `j=0` equation forces `P.coeff 0=1`,
  so `natDegree` on a zero polynomial adds no admissible witness.
- `ReducedPadeRepresentation` adds polynomial `IsCoprime P Q`. The test
  `Q.eval z≠0` is therefore the correct no-pole condition for the **reduced**
  quotient. Applying it to unreduced denominators would be stronger than
  the original target. The explicit reduced-pair existence conjunct for
  each order prevents an empty universal quantification. A future proof
  must actually construct a pair and justify cancellation/renormalization;
  neither is assumed by the definition.
- The universal conjunct covers **every** reduced normalized pair and every
  `z:ℂ` with `‖z‖≤3`, and requires both `Q.eval z≠0` and
  `‖1−P.eval z/Q.eval z‖≤2`. Complex norm is modulus, the disk boundary is
  included, and the weak `≤2` is essential: the source and exact order-one
  pair `P=1+5z/12`, `Q=1−z/12` give `P(3)/Q(3)=3` and error exactly `2`.
  No real-axis, finite-order, or smaller-disk restriction appears.

The existence-plus-`∀ P Q` formulation is mathematically faithful to the
canonical single rational approximant. Two normalized Padé pairs have
`P₁Q₂−P₂Q₁` of degree at most `2m` with all coefficients through `2m`
zero, hence represent the same rational function. Cancelling any common
factor is legitimate because `Q(0)=1`, so the factor is nonzero at zero;
renormalization restores denominator constant one without increasing
degrees or lowering the approximation order. These are mathematical
equivalence arguments and remain formal proof obligations. The source
theorem also treats `m=0` and a matrix spectral-radius corollary; neither is
part of the canonical scalar question or required in this frozen Target.

The live and frozen definitions are definitionally equivalent: a local Lean
file proved their equivalence by `Iff.rfl`. No target was replaced or
weakened in the pre-proof review.

## Exact numerical and source-proof checkpoints

The preserved manuscript's Theorem 1 states the full all-order result, with
strictness for `m≥2` and equality at `m=1,z=3`. Its analytic argument uses
the denominator coefficient estimate
`0<b_(m,j)≤S_m^j` for `1≤j≤m`, where
`S_m=Σ_{ν>m}1/(π²(ν−1/2)²)<1/(9m)`; at radius `R=3` the disk lemma requires
`2RS_m=6S_m<1`. The rational series estimate is
`f(3)≤6179/2120<35/12`. For every `m≥16`, `6S_m<1/24`, giving the strict
error bound `(f(3)−1)/(1−6S_m)<(23/12)/(23/24)=2`. The finite certificate
covers **each** `m=1,…,15`, so the analytic and finite ranges meet without a
gap. Its exact aggregate tests are

```text
B_m=Σ_{j=0}^m |q_(m,j)|3^j < 2,
N_m=Σ_{j=0}^m |p_(m,j)−q_(m,j)|3^j ≤ 2(2−B_m).
```

These imply `|Q(z)|≥2−B_m>0` and `|P(z)−Q(z)|≤N_m` on the full closed disk.
I inspected the manuscript and the standard-library verifier and reran
`python3 code/wave_kernel_certificate.py results/wave_kernel_finite_certificate.json --verify`
in its package root.
It exited zero and reported PASS for all 15 records and the rational
`f(3)` bound. This is independent reproducible **source evidence**, not a
Lean kernel check of those rational witnesses or the analytic proof. The
previous independent manuscript review is likewise an AI proof audit, not
formal certification.

## Lean boundary and feasibility

With the pinned Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran:

```sh
lake build NLA.Statements.MF03 Reviewed.MF03
lake env lean NLA/Statements/MF03.lean
lake env lean Reviewed/MF03.lean
lake env lean /private/tmp/mf03-statement-independent-audit.lean
```

All exited zero; Lake completed 1,874 jobs. The temporary audit imports
both modules, proves the live/frozen `Target` equivalence by `Iff.rfl`, and
runs their `#assert_statement` and `#assert_trust kernel` checks. Both axiom
reports list only `[propext, Classical.choice, Quot.sound]`. Those checks
establish **well-formed, trusted definitions**, not a theorem inhabiting
`Target`. There is no MF-03 proof module or Linux Comparator acceptance.

The pre-proof assessment correctly identifies a substantial feasibility
limit. Mathlib has semistandard Young tableau definitions, but my targeted
search of this pinned checkout found no Jacobi–Trudi/Schur identity or Padé
theorem that gives the manuscript's central denominator formula. A complete
Lean proof needs the all-order product/coefficient bridge and denominator
bound, rational analytic estimates, all 15 finite rational witnesses,
construction and reduction of the approximants, and transport to **every**
reduced pair. A short kernel check of the JSON alone would prove only the
finite orders. Proof work may begin under this approved statement, but no
axiom, `sorry`, or unverified imported manuscript claim can fill the
all-order gap.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `docs/lean/statements/MF-03/ORIGINAL.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `docs/lean/statements/MF-03/NUMERICAL_TARGETS.md` | `7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28` |
| `docs/lean/proofs/MF-03/STATEMENT_REVIEW.md` | `7c7d7c8de42fdf16aff0365dbcaf89586fdf87cd612c6ebab46cfa3b51e0ab41` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/Reviewed/MF03.lean` | `a0c55c3f315c5330d8da170fc2f4c8ac6dab715b8a30b0111660d262ea0d0674` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/results/wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `references/colbrook-matrix-functions-2026-09-11/code/wave_kernel_certificate.py` | `73587f8a4a5afd12bd6f33ae9ffb5b85c9388831cf152b48a4c64595f84c3155` |
| `references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-03-review.md` | `cccbb11ca9e42a0f27e72d3b351f76c66b5a06eee69f7c6e367ebab8e0c79423` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `/private/tmp/mf03-statement-independent-audit.lean` | `4bb31bd303692f3a17a8e93576e0026cd28ee49175412db72cf77db3d36b3303` |
