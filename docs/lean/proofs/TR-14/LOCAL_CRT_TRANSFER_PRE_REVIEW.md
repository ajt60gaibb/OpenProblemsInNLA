# TR-14 exact root factorization, CRT, and local Frobenius transfer: pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen for a separate mathematical review before Lean implementation. This contract bridges the audited normalized least-apolar quotient to the audited one-factor local Fourier identity. It does not yet assert a global symmetric width, the second upper bound, an ordinary lower bound, or the frozen `NLA.Statements.TR14.Target`.

## Root data with every multiplicity

Let `g∈ℂ[t]` be **monic** of exact degree `r≥1`. Write `M=g.roots`, the finite multiset of complex roots **with multiplicity**, and let `S=M.toFinset` be its support. For `α∈S`, define `ℓ_α=M.count α`. Algebraic closure and monicity give the exact facts

\[
 S\ne\varnothing,\qquad \ell_\alpha\ge1,\qquad
 g(t)=\prod_{\alpha\in S}(t-\alpha)^{\ell_\alpha},\qquad
 \sum_{\alpha\in S}\ell_\alpha=r.
 \tag{RF}
\]

The `α` values in `S` are distinct by construction, so the powers of their linear factors are pairwise coprime. Neither `S.card=r` nor `ℓ_α=1` is assumed. A multiplicity may exceed the tensor mode dimension `n`.

Put `A=AdjoinRoot g`, `t̄=AdjoinRoot.root g`, and `B_α=LocalTruncated ℓ_α=ℂ[z_α]/(z_α^{ℓ_α})`. The required **complex-algebra equivalence** is

\[
 E:A\ \simeq_{\!\mathbb C}\ \prod_{\alpha\in S}B_\alpha,
 \qquad E(t̄)_\alpha=\alpha+z_\alpha.
 \tag{CRT}
\]

In particular, for every `j≥0`, `E(t̄^j)_α=(α+z_α)^j`, and `E` preserves every finite product. This is an actual algebra equivalence, not a dimension-only isomorphism or an evaluation of a quotient class at a complex number. One exact construction is ideal CRT for the pairwise coprime ideals `⟨(X−C α)^ℓα⟩`, followed by each translation equivalence sending the class of `X−C α` to the nilpotent generator `z_α`. The identity `⟨g⟩=⋂_α⟨(X−C α)^ℓα⟩` must be proved from (RF) and coprimality. The shift has the inverse substitution `X↦X−α`; the local factor is specifically `ℂ[z]/z^ℓ`, as required by the audited local Fourier source.

## Exact transfer of the global moment functional

For the conditional quotient statement, take `D≥r`, a moment vector `h':Fin(D+1)→ℂ`, and the audited functional

\[
 \Lambda=\operatorname{quotientMomentFunctional}(h',g)
 :A\to_{\!\mathbb C}\mathbb C.
\]

Assume the **proved** all-moment identity

\[
 \Lambda(t̄^j)=h'_j\quad\text{for every }0\le j\le D,
 \tag{AM}
\]

and genuine global Frobenius nondegeneracy

\[
 \forall x\in A,\quad
   (\forall y\in A,\ \Lambda(xy)=0)\Longrightarrow x=0.
 \tag{GF}
\]

The audited `normalized_quotient_all_moments` and `quotientMomentFunctional_frobenius` derive (AM) and (GF) from a **nonzero** normalized moment vector and an exact monic least-degree apolar `g`; these are intermediate hypotheses only, not assumptions added to `Target`.

For each `α∈S`, let `ι_α:B_α→ₗ[ℂ]∏_βB_β` insert its argument in component `α` and zero elsewhere. Define

\[
 \Lambda_\alpha(x)=\Lambda(E^{-1}(\iota_\alpha x)).
 \tag{LC}
\]

The insertion is linear but **not unital** when `S` has more than one element. Its multiplication behavior with an arbitrary product tuple is the exact componentwise identity
`ι_α(x)·v=ι_α(x·v_α)`. These facts give, for every `x∈A`,

\[
 \Lambda(x)=\sum_{\alpha\in S}\Lambda_\alpha((Ex)_\alpha),
 \tag{SUM}
\]

because every product tuple is the sum of its supported components. Each `Λ_α` inherits genuine local Frobenius nondegeneracy: if `Λ_α(a b)=0` for every `b∈B_α`, then `E^{-1}(ι_α a)` pairs to zero with **every** `y∈A`, so (GF) makes that element zero and its `α` coordinate is `a=0`. No local nondegeneracy may be postulated without this argument.

Combining (AM), (CRT), and (SUM) yields the exact **all-moment** formula

\[
 h'_j=\sum_{\alpha\in S}
       \Lambda_\alpha((\alpha+z_\alpha)^j)
 \quad\text{for every }j\in Fin(D+1).
 \tag{LM}
\]

For the frozen zero-based Hankel setting `m≥3`, `n≥2`, `q=n−1`, `D=mq`, every index tuple `i:Fin m→Fin n` satisfies `∑_k i_k≤D`. Hence (LM), or the audited all-moment quotient mode pairing followed by (SUM), gives

\[
 (\operatorname{Hankel}h')_i
 =\sum_{\alpha\in S}\Lambda_\alpha\!\left(
       \prod_{k\in Fin m}(\alpha+z_\alpha)^{i_k}\right).
 \tag{HC}
\]

The equality must use **all** `j≤D`; agreement only on the first `r` power-basis moments cannot justify arbitrary frozen Hankel entries.

## Relation to chart normalization and the full target

The audited `normalize_chosen_minimal_apolar` starts from any nonzero moment vector and any nonzero least homogeneous apolar form, including one whose original projective root lies at infinity. It supplies an invertible chart, a nonzero transformed `h'`, and a monic affine `g` of exact degree `r`, retaining all lower zero apolar kernels. The audited `GL2WidthTransport` will return a later symmetric-width witness from `h'` to the original `h`. Thus this CRT gate works **after** the chart and excludes no original root-at-infinity case.

The audited chart modules do **not yet** identify the original form's projective root multiset, with multiplicities, with the affine root multiset of `g`. That precise root-correspondence lemma remains a separate obligation before the numerical expression `(m−1)r−(m−2)s` can be stated in terms of the original chosen projective form. No existing chart theorem is silently promoted to that stronger claim.

The next reviewed gate may apply the audited `local_fourier_mode_coordinates` to every `Λ_α` in (HC), then reindex the disjoint union of the `Fin N_α` nodes and prove

\[
 \sum_{\alpha\in S}N_\alpha
 =\sum_\alpha\bigl((m-1)(\ell_\alpha-1)+1\bigr)
 =(m-1)r-(m-2)|S|.
\]

This contract itself asserts neither that global width nor the full all-width equivalence. The frozen Target still quantifies over **all** `m≥3`, `n≥2`, moment vectors including zero, and widths `r`.

## Proposed narrow Lean boundaries

These are signature sketches; dependent product notation and exact type casts may be elaborated in source without altering the claims.

1. **Root multiset gate:** for `g.Monic` and `0<g.natDegree`, construct `S`, positive `ℓ`, (RF), and pairwise coprime factor ideals. Prove `S.card>0` and `∑ℓ=g.natDegree`. Do not collapse repeated roots into one copy each.
2. **Algebra CRT gate:** construct `E : AdjoinRoot g ≃ₐ[ℂ] (∀ α:S, LocalTruncated (ℓ α))`; prove `E (AdjoinRoot.root g) α = algebraMap ℂ _ α.val + localRoot (ℓ α)` and the power/product versions. A ring equivalence without complex-scalar compatibility would leave a gap in local `Λ_α` linearity.
3. **Local functional gate:** define `Λ_α` by supported insertion through `E.symm`; prove `Λ(x)=∑_αΛ_α((E x) α)` for every `x`, and derive every local Frobenius statement from (GF). Handle singleton `S` and arbitrary positive multiplicities.
4. **Moment/tensor gate:** with the actual audited `quotientMomentFunctional` and all-moment theorem, prove (LM) for every `Fin(D+1)` and (HC) for every frozen zero-based tensor index. This gate may assume the previously **proved** `E` and (GF) as local theorem parameters, but the eventual nonzero-`h'` corollary must discharge them from factorization and minimal apolarity.

The module sequence may be split into small unimported sources. Each exact source must be frozen, independently reviewed, imported only after LeanCert kernel trust and transitive axiom checks, and built with the pinned Lean version. No new axiom, sorry, floating approximation, root genericity, or changed problem ID/Target is allowed.

## Endpoint and numerical self-check

- `r=1`: `S={α}`, `ℓ_α=1`, `A≃ℂ`, `z_α=0`, and (LM) reads `h'_j=Λ_α(α^j)`. There is one local factor and one Fourier node for every `m≥3`.
- A single repeated root `g=(t−α)^r`: `S` is a singleton, `ℓ_α=r`, and `E` is the translation equivalence. It remains valid when `r>n`; no local dimension restriction is inserted.
- Mixed multiplicities, for example `(t−α)^3(t−β)^2` with `α≠β`: `r=5`, `|S|=2`, the local dimensions sum to five, and the two local functionals are supported in different CRT coordinates. The later node count is `((m−1)·2+1)+((m−1)·1+1)=(m−1)·5−(m−2)·2`.
- A balanced least-apolar kernel may contain more than one chosen form; the CRT construction applies to **each** chosen monic chart polynomial separately, and the root count may depend on that choice. No uniqueness of the chosen apolar form is assumed.
- `h=0` is excluded from the nonzero least-apolar/Frobenius route and is handled by audited width-zero facts. Any original root at infinity is moved by the audited invertible chart; its multiplicity preservation still requires the separate correspondence lemma above.

## Exact source locks

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` §§2–3 | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| Audited `GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |
| Audited `GL2WidthTransport.lean` | `5a50bb7984b3a9dd034faae43ab088f4ec10880ce37128cad9afd79af1a528a4` |
| Audited `MomentQuotientModePairing.lean` | `24adc0f2e21ee8f84deb8ef4d6eddc8cc056327c2601e69f7c4a2a2cb35ae6cf` |
| Audited `LocalFourierOneFactor.lean` | `3b0e9c148f6a01c6392c370c5949d4ab4ccd84552d1844cec7aa3ebef084f516` |
| Audited `LocalFourierMode.lean` | `ab77987b8b5448ef24f59ca6c49a2598011f3b13babda48ca9cb09febe2c6626` |
| Approved `LOCAL_FOURIER_UPPER_PRE_REVIEW.md` | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Approved `LOCAL_ONE_FACTOR_FOURIER_PRE_REVIEW.md` | `9bfa860893d7a7d049ea1c9ced1a508d2c10eed430680e95bd2dee3e9e51cc91` |

An independent mathematical review must verify this **exact** text before any CRT Lean source. In particular, check the multiplicity count, algebra/scalar compatibility, the supported-insertion Frobenius argument, every moment through `D`, and the explicit open projective-root correspondence. Changed bytes reopen the review. Canonical ID, README, and frozen Target remain unchanged.
