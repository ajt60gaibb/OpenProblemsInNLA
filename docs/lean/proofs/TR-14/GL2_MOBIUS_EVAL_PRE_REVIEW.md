# TR-14 exact nonzero affine-root coordinate under the audited chart

**Status:** source-locked proposal for independent mathematical and numerical
review before any Lean implementation. This is one narrow next gate after the
audited full affine chart polynomial identity. It does not assert preservation
of root multiplicities, a projective root count, a tensor width, or the frozen
TR-14 Target.

## Proposed public Lean signature

```lean
theorem chart_dehomogenize_eval_nonzero
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : ℂ) (ht : t ≠ 0) :
    (dehomogenize d (transportedApolarVector z d g)).eval t =
      t ^ d * (dehomogenize d g).eval (z + t⁻¹)
```

The identity is exact over `ℂ` for every ambient homogeneous degree `d`,
including `d=0`, every coefficient vector `g`, including zero and trailing
zeros, and every `z`. Only `t≠0` is required because the displayed inverse is
the nonzero affine coordinate map. There is no assumption that the original
affine polynomial is monic or that `g` is apolar.

## Mathematical and numerical check

Let `p(t)=Σ_{i=0}^d g_i t^i` and let `p_z(t)` be the actual dehomogenization of
the transported coefficient vector. The audited chart identity gives

```text
p_z(t)=Σ_{i=0}^d g_i t^(d−i)(1+zt)^i.
```

For `t≠0`, `1+zt=t(z+t⁻¹)`, hence each summand is exactly
`g_i t^d(z+t⁻¹)^i`; summing proves the proposed identity. The exponent is
the original homogeneous degree `d`, not `p.natDegree`, so trailing-zero
coefficients and an original root at infinity remain represented. No binomial
coefficient, conjugation, complex norm, approximate root, or branch choice is
introduced.

For `d=2` and `g=(a,b,c)`, the audited polynomial is
`c+(b+2cz)t+(a+bz+cz²)t²`. The proposed right side is exactly
`t²[a+b(z+t⁻¹)+c(z+t⁻¹)²]`, which expands to the same polynomial at each
`t≠0`. At `d=0`, both sides equal `g₀`. At `z=0`, the statement is the exact
reciprocal identity `p_0(t)=t^d p(t⁻¹)`.

The immediate future root consequence is precise but **not** part of this
gate: since `t^d≠0` for `t≠0`, `p_z(t)=0` iff `p(z+t⁻¹)=0`. If an original
finite root is `α≠z`, its chart coordinate is `t=(α−z)⁻¹`, and this map is
invertible on the indicated domains. The exceptional coordinate `t=0`
corresponds to the original point at infinity and must be handled separately.
When `p(z)≠0`, the selected chart has no transformed root at infinity, but
that condition is not needed for this scalar identity. A later exact theorem
must still prove multiplicity preservation and combine the finite-root and
infinity cases before replacing the normalized local CRT support count by the
number of distinct projective zeros of the originally chosen apolar form.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/NLA/Proofs/TR14/GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| `lean-statements/NLA/Proofs/TR14/GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| `lean-statements/NLA/Proofs/TR14/GL2Dehomogenize.lean` | `3de97ab8ba4f9733fe6e876808f9d6ea9c0e1d33ff9ddea9219baf09aeda9af5` |
| `lean-statements/NLA/Proofs/TR14/GL2AffineChartPolynomial.lean` | `b0ec8b4adc5fc3afb79baf0e7fc462079e86cdd987f88ff0e979f3d05a5bee85` |
| `lean-statements/NLA/Proofs/TR14/GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTRootData.lean` | `96d8d86b6e15c024978d44b78aa525dc0cbb1231fd09d274c1c0c32242c9a263` |

Implementation, only after independent approval, belongs in a new unimported
Lean module. It must prove this exact signature using the audited formula and
pass pinned LeanCert kernel plus an imported exact-signature audit with only
standard axioms. The canonical ID, README, solution source and frozen Target
remain unchanged.
