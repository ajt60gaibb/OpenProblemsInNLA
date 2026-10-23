# TR-14 binary symmetric upper bound: proposed pre-proof contract

**Author:** `/root/tr14_proof_route` (AI agent), 16 October 2026. **Status:** draft for an independent mathematical and exact-signature review before Lean implementation. This contract covers Proposition “Binary interpolation upper bound” in the canonical `solution.tex`, Section 3. It neither proves nor changes the frozen `NLA.Statements.TR14.Target`.

## Source and frozen boundary

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/Reviewed/TR14.lean` | `9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356` |

Let `q=n−1`, `D=mq`, `r₀` be the degree of a chosen least nonzero homogeneous apolar form, and `v=D−r₀+2`. The selected form may have an infinity root in the original coordinates; the audited binary chart first makes its affine polynomial `g` monic of exact degree `r₀`. The theorem must cover every nonzero complex moment vector, including balanced and repeated-root cases, with `m≥3` and `n≥2`. It is an upper bound on *actual symmetric width*, with arbitrary complex scalar weights; no squarefree, generic, distinct-root, or Vandermonde premise is added to the final statement.

## Proposed exact Lean boundary

The normalized-chart theorem should have the following mathematical signature, using the existing definitions verbatim. Names and proof-module split may change, but no hypothesis or conclusion may be weakened.

```lean
theorem binary_symmetricWidth_of_minimal {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0)
    (g : Polynomial ℂ) (hg : g.Monic)
    (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ m * (n - 1))
    (hrHi : g.natDegree ≤ (m * (n - 1)) / 2 + 1)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1),
      d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ,
        IsApolar h d hd b → b = 0) :
    NLA.Statements.TR14.SymmetricWidth
      (NLA.Statements.TR14.Hankel h)
      (m * (n - 1) - g.natDegree + 2)
```

`hrHi` is supplied by audited `minimal_apolar_exists`, not assumed in the frozen Target. It gives `v≥r₀` and `v−r₀=D−2r₀+2≥0`, including the balanced endpoint `D=2r₀−2`, where `v=r₀` and the auxiliary form `Q` has degree zero. `hrPos` gives `v≤D+1`; for `r₀≥2`, `v≤D`, so the existing degree-`v` `IsApolar` API applies. For `r₀=1`, `v=D+1`: the source's apolar conditions `0≤j≤r₀−2` are empty and its `I_d` convention is the whole degree-`d` space for `d>D`. Since the current Lean API only defines `IsApolar` for `d≤D`, the implementation may prove a direct rank-one symmetric witness from the one-dimensional Frobenius quotient and pad it to `v`, or introduce a proved vacuous `d>D` extension. It must not silently call `IsApolar` at an unavailable degree.

The original-coordinate corollary takes the `minimal_apolar_exists` output `r₀`, `hrD`, `hrPos`, `hrHi`, a nonzero coefficient vector `G : Fin (r₀+1)→ℂ`, its apolarity, and all lower-kernel vanishing. It uses `normalize_chosen_minimal_apolar` to obtain `z` and monic `g` with `g.natDegree=r₀`, applies the normalized theorem to `transformedMoments z h`, and uses `chart_symmetricWidth_reverse` to return `SymmetricWidth (Hankel h) (D−r₀+2)`. There is no chart premise on the original `h` or change to the frozen Target.

## Mathematical obligations and exact endpoints

The apolar-pencil obligations below apply when `r₀≥2`, so `v≤D`. The `r₀=1` case follows the separate one-dimensional quotient construction described above and must still produce the same final width `v=D+1`.

1. On `A=ℂ[t]/(g)`, let `τ` read the coefficient of `t^(r₀−1)` in the unique remainder of degree `<r₀`. Prove `τ` Frobenius: if a remainder has leading degree `d<r₀`, its product with `t^(r₀−1−d)` has nonzero top coefficient. The existing `quotientMomentFunctional` is a Frobenius functional `λ` and matches `h_j` for every `0≤j≤D`. The Frobenius pairings identify a unique `u∈A` with `λ(a)=τ(ua)` for all `a`; prove `u` is a unit, rather than postulating it.
2. Let `b(t)` be the degree-`<r₀` representative of `u⁻¹`. For every `0≤j≤r₀−2`, show `L(t^j b)=λ([t^j b])=τ([t^j])=0`. The product degree is at most `2r₀−3≤D` for `r₀≥2`, so the existing full moment match is in range. Homogenize to the degree-`v` binary form `B(X,Y)=X^v b(Y/X)` and prove its exact apolar equations for all shifts `0≤j≤D−v=r₀−2`. Prove `B` is coprime to the original normalized homogeneous `G`: the class of `b` modulo `g` is a unit, and monic `G` has no root at infinity.
3. Choose a homogeneous `Q` of degree `v−r₀` such that `GQ` is coprime to `B` and `Q` has no zero at infinity. This includes `v=r₀`, when `Q` is a nonzero constant. Prove the pencil `B+cGQ` has some member that is squarefree and has no root at infinity. The source's argument uses the nonconstant characteristic-zero rational function `B/(GQ)`: finitely many finite critical values are excluded, as is `c=0`. The selected member has affine degree exactly `v`, `v` distinct finite roots `β₁,…,β_v`, and remains apolar because both `B` and `GQ` are apolar. The latter needs proof from the apolar ideal/recurrence, not an assumption.
4. Solve the invertible `v×v` Vandermonde system for weights `γ_a` matching precisely `h_0,…,h_(v−1)`. The last initial index is within the supplied moment vector because `v≤D+1`. Use the monic apolar recurrence of the selected degree-`v` polynomial at every shift `0≤j≤D−v` to prove the Vandermonde moments equal `h_j` for *all* `0≤j≤D`. If `v=D+1`, this range is empty and the initial system already matches every supplied moment.
5. Define the actual frozen symmetric witness with `c_a=γ_a` and `v_a(i)=β_a^i` for each `i:Fin n`. For every tuple `i:Fin m→Fin n`, its product is `β_a^(Σ_k(i k).val)`, so the all-moment equality at `HankelIndex i` proves the coordinate equation in `SymmetricWidth`. The witness has exactly `v` slots; zero weights remain legal. The chart transport keeps the same width and one repeated mode vector per slot.

## Existing inputs and new work

`ApolarMinimal` supplies least degree and `r₀≤D/2+1`; `GL2ChartNormalize` and `GL2ApolarTransport` supply monic chart normalization and lower-kernel transport; `NormalizedQuotient` supplies all moments through `D`; `FrobeniusMinimal` supplies nondegeneracy; `GL2Homogeneous` and `GL2CoefficientBasis` provide genuine binary forms and their coefficient basis; `MomentQuotientModePairing` identifies the frozen Hankel multilinear form; `GL2WidthTransport` returns symmetric width to the original chart. `WidthBasics` presently proves zero-width and symmetric-to-ordinary facts, but no general width padding theorem. The top-remainder representation, inverse-unit construction, coprime/squarefree pencil, Vandermonde reconstruction, rank-one endpoint, and final padding are **new proof obligations**. The existing local CRT/Fourier upper construction is separate and cannot replace this binary branch.

Implementation should follow an independent review of this exact contract. Every resulting module needs a pinned Lean build, imported LeanCert kernel trust and transitive axiom report, source/signature review against the locked mathematical proof, and eventual isolated Comparator verification before any full-target claim. This pre-review contract supports only one symmetric upper branch; the unrestricted ordinary lower bound and all-width `Target` remain open.
