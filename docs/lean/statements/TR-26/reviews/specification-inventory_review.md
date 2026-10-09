# TR-26 pre-implementation specification: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This checks fidelity of the proposed statement, not a Lean implementation or an independent proof of the source theorem.

I compared the complete canonical README, its byte-identical `ORIGINAL.md` copy, the proposed specification, and Theorem 1 and the incidence discussion in the resolution manuscript. The specification retains the exact unweighted rational normal curve for every `d≥2`, its point at infinity, the complete projective space of nonzero complex symmetric matrices, and the bilinear quotient `zᵀHz/zᵀz` without conjugation. It defines criticality along the curve, forms the full critical-incidence **Zariski closure**, and uses the Jacobian of generators of that full ideal in the `d+1` curve coordinates with the source's rank bound `≤d−1`.

The isotropic part is the matrix projection of the ramification locus at `zᵀz=0`, while the nonisotropic part is the Zariski closure of the projection with `zᵀz≠0`. The specification keeps those different closure operations and asks for both loci to be reduced projective hypersurfaces, with exact degrees `2d` and `6(d−1)` respectively, for every `d≥2`. It does not substitute the known total degree or a weighted embedding. I found no missing component, altered multiplicity convention, or reduced numerical range.

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-26/README.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/NUMERICAL_TARGETS.md` | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.md` | `4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8` |
