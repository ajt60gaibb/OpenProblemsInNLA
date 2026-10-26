# TR-26 independent pre-implementation specification review

**Verdict: APPROVE.** I did not author the specification. I checked it independently against the complete canonical README, generated original TeX, and Colbrook's resolution manuscript. This approves an exact statement target, not the proof or a future Lean implementation.

| Reviewed input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-26/README.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/NUMERICAL_TARGETS.md` | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |
| `tensor-computations/TR-26/problem.tex` | `83231398ab43af3ccad0dfc6febcc93c6fd9a02d66b595af69fc285306af6426` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.md` | `4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8` |

The canonical README and retained `ORIGINAL.md` are byte identical. The permanent ID and path are unchanged.

The specification retains **every** `d≥2`, the standard unweighted Veronese coordinates through the point at infinity, complex symmetric matrices modulo nonzero scalar, and the bilinear forms `zᵀHz` and `zᵀz` without conjugation. Criticality is taken along the curve only, on the open set where the denominator is nonzero. The incidence is the Zariski closure in the product; it is not defined by assigning an artificial value to a zero denominator.

The Jacobian rank condition is applied to homogeneous generators of the **full** defining ideal of that incidence in the `d+1` curve coordinates, with rank at most `d−1`. This is the canonical ramification definition. The isotropic part is exactly the projective projection `π(𝓑∩Q)` with no extra closure inserted, while the nonisotropic part is the Zariski closure of `π(𝓑\Q)`. The distinction matters at isotropic boundary points and matrix parameters in the numerator-map kernel. Reduced projective-set degree includes every component and does not count eliminant multiplicities.

Both requested parts remain simultaneous: each is a projective hypersurface, `deg Σ_noniso=6(d−1)` and `deg Σ_iso=2d`, including `d=2` with degrees six and four. The known total `2(4d−3)` is not used in place of the split. No genericity qualifier, approximation, or probability condition has been introduced. A later Lean boundary will need concrete projective/ideal/Jacobian/projection/degree meaning; the specification explicitly rejects opaque stand-ins. I found no projective, Jacobian, or degree mismatch requiring revision.
