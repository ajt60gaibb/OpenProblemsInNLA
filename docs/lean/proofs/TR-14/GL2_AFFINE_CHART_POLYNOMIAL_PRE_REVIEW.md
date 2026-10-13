# TR-14 exact affine polynomial under the audited binary chart

**Status:** one proposed missing mathematical gate for independent review
before any Lean implementation. It supplies the full affine polynomial
identity behind the existing last-coefficient chart lemma. It does not
claim root multiplicity invariance, a tensor width, or the frozen Target.

## Proposed public Lean signature

```lean
theorem dehomogenize_transportedApolarVector
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    dehomogenize d (transportedApolarVector z d g) =
      ∑ i : Fin (d + 1),
        Polynomial.C (g i) * Polynomial.X ^ (d - i.val) *
          (1 + Polynomial.C z * Polynomial.X) ^ i.val
```

The equality is in `Polynomial ℂ` for every `d`, including `d=0`, and
every coefficient vector `g`, including zero and vectors whose final
coefficient vanishes. No apolarity or genericity hypothesis is added.

## Source and exact indexing

The audited basis `binaryMonomial d i` is
`X^(d−i.val) Y^i.val`, with `i : Fin(d+1)`. The audited chart
substitution is `(X,Y) ↦ (Y, X+zY)`; its determinant is `−1`, so it
is invertible. Consequently the transformed homogeneous form is

```text
G_z(X,Y) = G(Y,X+zY)
         = Σ_{i=0}^d g_i · Y^(d−i) · (X+zY)^i.
```

Dehomogenizing at `(X,Y)=(1,t)` gives exactly

```text
G_z(1,t) = Σ_{i=0}^d g_i · t^(d−i) · (1+zt)^i,
```

which is the proposed polynomial identity. There is no coefficient
reversal beyond the displayed `d−i`, no complex conjugation, and no
binomial multiplier outside the polynomial power. Each summand has
degree at most `d`; the `i=0` term is `g₀ t^d`, and the `i=d` term is
`g_d(1+zt)^d`. The statement therefore preserves every trailing-zero
and original-infinity-root case.

The previously audited `chart_last_coefficient` is the leading
coefficient consequence: the coefficient of `t^d` equals
`Σ_i g_i z^i = (dehomogenize d g).eval z`. If this value is nonzero,
the transformed polynomial has exact degree `d`, which is the chart
normalization used in `normalize_chosen_minimal_apolar`. At `d=0`,
both sides are the constant polynomial `g₀`; at `z=0`, the formula is
the exact reversal `Σ_i g_i t^(d−i)`. These are indexing checks, not
specialized proof cases.

This identity is a tractable next step toward comparing the affine
roots of a normalized chart polynomial with the distinct projective
roots, including infinity, of the original homogeneous apolar form.
That root/multiplicity correspondence is **not** concluded here.
It remains necessary before the local Fourier count can be expressed
using the original form's projective-root number in the canonical
nonzero-rank formula. The second symmetric upper construction and the
arbitrary ordinary-width lower bound also remain open.

The canonical `solution.tex` §2 states that a binary linear change
preserves projective multiplicities and chooses a chart with no root at
infinity. The exact polynomial formula above records the audited
chart's action needed for a later kernel proof of that assertion.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/NLA/Proofs/TR14/GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| `lean-statements/NLA/Proofs/TR14/GL2CoefficientBasis.lean` | `548b46a87516484b75022bd5d0d901132ab37762d4991ebb09eeec5b0f509a2f` |
| `lean-statements/NLA/Proofs/TR14/GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| `lean-statements/NLA/Proofs/TR14/GL2Dehomogenize.lean` | `3de97ab8ba4f9733fe6e876808f9d6ea9c0e1d33ff9ddea9219baf09aeda9af5` |
| `lean-statements/NLA/Proofs/TR14/GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |

Implementation, if independently approved, belongs in a new module.
The canonical ID, README, `solution.tex`, and frozen
`NLA.Statements.TR14.Target` remain unchanged. The theorem must pass
an imported exact-signature LeanCert kernel audit with only standard
axioms; no `sorry`, custom axiom, unsafe declaration, `native_decide`,
or approximate root computation is permitted.
