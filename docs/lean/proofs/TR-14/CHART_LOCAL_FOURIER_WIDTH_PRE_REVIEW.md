# TR-14 original-coordinate transport of the local Fourier width

**Status:** one exact source-locked mathematical and numerical gate proposed
for independent review before Lean implementation. It composes two already
audited theorems, retaining the frozen tensor, width predicate, and chart
conventions. It is an upper-bound gate, not the full `TR14.Target`.

## Proposed public Lean signature

```lean
theorem chart_localCRTFourier_symmetricWidth {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (z : ℂ)
    (g : Polynomial ℂ) (hg : g.Monic)
    (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ m * (n - 1))
    (hhTrans : transformedMoments z h ≠ 0)
    (hAp : IsApolar (transformedMoments z h) g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1),
      d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ,
        IsApolar (transformedMoments z h) d hd b → b = 0) :
    NLA.Statements.TR14.SymmetricWidth
      (NLA.Statements.TR14.Hankel h)
      ((m - 1) * g.natDegree -
        (m - 2) * (localRootSupport g).card)
```

The theorem's conclusion concerns the **original** moment vector `h`,
not the transformed vector. The affine root support in the numerical
width is deliberately that of the selected monic chart polynomial `g`.
This gate makes no identification with the distinct projective roots of
an original homogeneous apolar form.

## Exact derivation and numerical content

Set `q=n-1`, `D=m*q`, and

```text
R=(m−1)·deg(g)−(m−2)·|localRootSupport(g)|.
```

The audited `localCRTFourier_symmetricWidth_of_minimal` takes exactly
`hm`, `hn`, `transformedMoments z h`, `hhTrans`, `g`, its monicity,
positive degree, degree bound, actual apolar equation, and all
lower-degree zero apolar kernels. It constructs the frozen
`SymmetricWidth (Hankel (transformedMoments z h)) R`. Its local node
count is the exact natural-number identity

```text
R = Σ_{α∈localRootSupport(g)} ((m−1)(ℓα−1)+1),
Σα ℓα = deg(g).
```

Thus the subtraction in `R` is nonnegative by a proved equality to a
finite cardinal; no truncated subtraction is silently treated as
integer arithmetic. Multiplicities `ℓα>n` and repeated roots are
retained, and every local term uses the audited root-of-unity coefficient
and the same mode vector in all `m` factors.

The audited `chart_symmetricWidth_reverse z m q R h` transports that
exact width from `transformedMoments z h` to `h`, applying the same
inverse chart factor map in every mode and keeping each scalar
coefficient. Since `2≤n`, `q+1=(n−1)+1=n`; this is the only index cast
needed to match its `Fin (q+1)` coordinate type with the frozen
`Fin n` target. No conjugation, binomial coefficient, normalization
factor, or extra summand is introduced by chart transport.

This proves an original-coordinate symmetric decomposition at **one
exact width** `R`. It does not claim every larger width, the second
`D−deg(g)+2` upper bound, an ordinary-width lower bound, equality of
minimum ranks, or the all-width target. The hypotheses describe a
normalized chart already supplied for a nonzero original tensor by
the separately audited `normalize_chosen_minimal_apolar`; that
existential discharge is a later gate and is not smuggled into this
signature.

## Endpoint checks

- `m=3,n=2` gives `q=1`, `D=3`; the signatures retain all four
  moments and the original `Fin 2` mode coordinates.
- `deg(g)=1` gives one affine root of multiplicity one and `R=1`.
- One root of multiplicity `ℓ` gives `R=(m−1)(ℓ−1)+1`, including
  `ℓ>n`; the local nilpotent construction remains essential.
- Several repeated roots contribute one exact local count per root;
  no squarefree premise appears.
- A root at infinity in the original homogeneous form is allowed by
  the audited chart normalization, but this conditional theorem counts
  only the affine roots after the chosen invertible chart. Projective
  multiplicity correspondence remains open.
- The zero tensor is outside the least-apolar hypotheses here and is
  covered separately by frozen width-zero semantics in a future
  all-width proof.

The canonical solution's local interpolation proposition (§3) gives
the displayed count. Its §2 coordinate-change discussion says a
linear binary change acts invertibly and identically on each mode.
The proposed theorem uses the two audited Lean versions of precisely
those steps. There is no numerical approximation or per-order
computation.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFourierWidth.lean` | `8359bed454116aa646f292050454b0e7ea39520e293826a8be5d31ac5ddcde3c` |
| `lean-statements/NLA/Proofs/TR14/GL2WidthTransport.lean` | `5a50bb7984b3a9dd034faae43ab088f4ec10880ce37128cad9afd79af1a528a4` |
| `lean-statements/NLA/Proofs/TR14/GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |
| Approved `LOCAL_CRT_FOURIER_GLOBAL_PRE_REVIEW.md` | `9a2f693fd8ad6be0a26b0dc1d2d88e0afc65adf32dd9cf2b386aaf074aa954ee` |
| Approved `GL2_CHART_TRANSPORT_PRE_REVIEW.md` | `5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322` |

Implementation, if approved, belongs in a new module with the frozen
Target and all listed sources unchanged. Its exact imported signature
must be independently audited under pinned LeanCert kernel trust with
only the standard axioms `[propext, Classical.choice, Quot.sound]`.
