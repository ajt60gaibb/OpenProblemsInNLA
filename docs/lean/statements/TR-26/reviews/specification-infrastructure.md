# TR-26 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the TR-26 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is a statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-26/README.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/NUMERICAL_TARGETS.md` | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |

The canonical README and retained `ORIGINAL.md` are byte identical. The permanent ID and path match `problem_ids.json`.

## Scheme and geometry comparison

The specification keeps the fixed unweighted Veronese parametrization `[a^d:a^(d−1)b:…:b^d]` of the full rational normal curve, including infinity, for every `d≥2`. It retains the full projective space of symmetric complex `(d+1)×(d+1)` matrices and the **bilinear**, unconjugated numerator and denominator. These choices determine the source's exact model; replacing them by a weighted embedding or Hermitian quotient would change the target.

The source first takes the Zariski closure of the nonisotropic critical-point correspondence in the product of curve and matrix parameter space. The specification preserves this order and requires criticality along the curve. Its ramification locus uses the rank-`≤d−1` Jacobian of homogeneous generators of the **full defining ideal of that closed incidence**, differentiated in all `d+1` curve coordinates. That keeps both the curve equations and critical equation in the conormal calculation. I checked the resolution manuscript's local explanation: the curve contributes `d−1` independent normal equations, and the final critical derivative supplies the remaining rank when unramified. Thus the threshold and source geometry agree. The specification does not silently replace the source's scheme with a convenient set of equations.

The isotropic divisor is exactly `zᵀz=0`. The spec distinguishes the two projections as written: `Σ_iso=π(𝓑∩Q)` **without** an added closure, and `Σ_noniso=ZariskiClosure(π(𝓑\Q))`. It requires reduced projective degree of each set, including all components and excluding eliminant multiplicity. The claim is that **both** are hypersurfaces with exact degrees `2d` and `6(d−1)` respectively for every `d≥2`, including degrees four and six at `d=2`. The known total degree is kept only as context. No probability, tolerance, finite test range, generic metric, or extra irreducibility theorem is substituted. I found no scheme, projection, endpoint, degree, or quantifier mismatch.
