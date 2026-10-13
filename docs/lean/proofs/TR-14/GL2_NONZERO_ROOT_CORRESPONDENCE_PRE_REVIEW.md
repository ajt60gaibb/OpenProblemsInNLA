# TR-14 nonzero finite-root correspondence for the audited binary chart

**Author:** `/root/tr14_root_correspondence` (AI agent), 11 October 2026.
**Status:** exact mathematical, numerical, and Lean-signature proposal for an
independent review **before** implementation. No Lean source for this gate has
been written. This is a partial chart result, not projective multiplicity
invariance, a projective support count, a rank bound, or the frozen TR-14
`Target`.

## Exact proposed public declarations

Write `p = dehomogenize d g` and
`q = dehomogenize d (transportedApolarVector z d g)`. The first theorem is the
zero-set consequence of the audited nonzero evaluation identity:

```lean
theorem chart_root_eval_zero_iff
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : ℂ) (ht : t ≠ 0) :
    (dehomogenize d (transportedApolarVector z d g)).eval t = 0 ↔
      (dehomogenize d g).eval (z + t⁻¹) = 0
```

The second declaration makes the **two-sided** correspondence explicit. Its
forward map sends an original finite root `α ≠ z` to
`t = (α - z)⁻¹`; its inverse sends a transformed finite nonzero root `t`
to `α = z + t⁻¹`. These maps, not merely an arbitrary equivalence of the
two subtypes, are part of this contract.

```lean
noncomputable def chart_nonzero_finite_roots_equiv
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    { α : ℂ // α ≠ z ∧ (dehomogenize d g).eval α = 0 } ≃
      { t : ℂ // t ≠ 0 ∧
        (dehomogenize d (transportedApolarVector z d g)).eval t = 0 }

theorem chart_nonzero_finite_roots_equiv_apply
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (α : { α : ℂ // α ≠ z ∧ (dehomogenize d g).eval α = 0 }) :
    (chart_nonzero_finite_roots_equiv z d g α).val = (α.val - z)⁻¹

theorem chart_nonzero_finite_roots_equiv_symm_apply
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : { t : ℂ // t ≠ 0 ∧
      (dehomogenize d (transportedApolarVector z d g)).eval t = 0 }) :
    ((chart_nonzero_finite_roots_equiv z d g).symm t).val = z + t.val⁻¹
```

The quantified `d` is the **ambient homogeneous degree**, including `d = 0`.
The coefficient vector may be zero or have trailing zeros. No monicity,
apolarity, chosen chart, nonzero polynomial, or `p.eval z ≠ 0` premise is
needed for these pointwise and subtype statements. Evaluation equality is
used directly, so even the zero-polynomial case is unambiguous; a later
finite-support cardinality argument must require a nonzero form.

## Mathematical derivation and domain check

The audited `chart_dehomogenize_eval_nonzero` states, for `t ≠ 0`,

```text
q(t) = t^d p(z + t⁻¹).
```

Over `ℂ`, `t^d ≠ 0` for every `d` and `t ≠ 0`, including `d = 0` where
`t^0 = 1`. Consequently `q(t)=0` iff `p(z+t⁻¹)=0`. For `α ≠ z`,
`α-z ≠ 0`, so `t=(α-z)⁻¹ ≠ 0` and
`z+((α-z)⁻¹)⁻¹ = α`. Conversely, for `t ≠ 0`,
`(z+t⁻¹)-z=t⁻¹ ≠ 0` and
`((z+t⁻¹)-z)⁻¹=t`. The displayed equations prove the specified
two-sided equivalence, with neither an extra root nor a lost eligible root.

The substitution is inherited from the actual audited binary chart
`G_z(X,Y)=G(Y,X+zY)` and its dehomogenization at `(1,t)`. It carries no
complex conjugation, coefficient reversal beyond the existing chart formula,
root approximation, or division by a potentially zero number. It retains
the exponent `d` rather than replacing it with `p.natDegree`; trailing zeros
are therefore not discarded.

This gate deliberately omits `t=0`: in homogeneous coordinates that point
maps to the original point at infinity. It also omits the original finite
point `α=z`, whose image lies at infinity in the transformed chart. Thus the
subtypes are exactly the corresponding **nonzero finite** charts. The formula
`q(0)=g_d` and the transformed leading coefficient `p(z)` are established
or available from separate audited chart identities, but the proposed
declarations do not assert any projective-infinity correspondence. They do
not compare multiplicities or count roots, and cannot yet replace the
original projective-root number `s` in the canonical nonzero rank formula.

## Exact numerical and boundary checks

At ambient degree `d=2`, take `p(u)=u²-u-2=(u-2)(u+1)` and `z=1`. The
audited polynomial formula gives `q(t)=1+t-2t²`. The two original finite
roots `α=2,-1` map respectively to `t=(2-1)⁻¹=1` and
`t=(-1-1)⁻¹=-1/2`; these are exactly the two zeros of `q`, and the
inverse `1+t⁻¹` returns `2,-1`.

Trailing zeros must still be represented. With `d=2`, `p(u)=u-2`, and
`z=1`, the chart gives `q(t)=t-t²`; the eligible original root `α=2`
corresponds to `t=1`. The additional root `t=0` reflects the original
homogeneous root at infinity and is intentionally outside the declared
equivalence. With `d=2`, `p(u)=u-1`, and `z=1`, the root `α=z=1` is
excluded, the chart polynomial is `q(t)=t`, and the transformed leading
coefficient vanishes: the excluded root has moved to transformed infinity.
For `d=0`, nonzero constant forms have no roots on either subtype, while
the zero form yields the same inverse-coordinate bijection on all points in
the two punctured affine domains.

## Source and prerequisite locks

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` (§2 binary chart; projective root count in the exact algorithm) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` (frozen all-width `Target`) | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/NLA/Proofs/TR14/GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| `lean-statements/NLA/Proofs/TR14/GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| `lean-statements/NLA/Proofs/TR14/GL2Dehomogenize.lean` | `3de97ab8ba4f9733fe6e876808f9d6ea9c0e1d33ff9ddea9219baf09aeda9af5` |
| `lean-statements/NLA/Proofs/TR14/GL2AffineChartPolynomial.lean` | `b0ec8b4adc5fc3afb79baf0e7fc462079e86cdd987f88ff0e979f3d05a5bee85` |
| `lean-statements/NLA/Proofs/TR14/GL2MobiusEval.lean` (kernel-audited evaluation identity) | `a6ce893b0bf5d7c0fed32d3bff8224ad893fe9d94ed3a63590b06b00ea4ad737` |
| `lean-statements/NLA/Proofs/TR14/GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |

After an independent mathematical and numerical review approves **this exact
document hash**, implementation may proceed in a new Lean module importing
`GL2MobiusEval`. A separate imported exact-signature audit must inspect the
forward and inverse coordinate maps, compile with pinned Lean 4.33.1 and
LeanCert `kernel`, and report the transitive axioms. No `sorry`, `admit`,
custom axiom, `unsafe`, `native_decide`, or approximate root computation is
allowed. The canonical TR-14 ID, README, proof source, and frozen Target
remain unchanged.
