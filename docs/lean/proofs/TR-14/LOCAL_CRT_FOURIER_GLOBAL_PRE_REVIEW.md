# TR-14 exact local CRT/Fourier sum: pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen for separate mathematical review before Lean implementation. This gate derives one symmetric upper construction for a normalized chart. It does not assert the second upper construction, either lower bound, original-coordinate projective root count, or the frozen full `NLA.Statements.TR14.Target`.

## Exact setting and inputs

Fix `m≥3`, `n≥2`, `q=n−1`, `D=mq`. Let `h:Fin(D+1)→ℂ` be **nonzero** and `g∈ℂ[X]` be monic of exact degree `r=g.natDegree≥1`, with `r≤D`. Require the actual frozen apolar equations

\[
 \operatorname{IsApolar}(h,r,g.\operatorname{coeff})
\]

and the exact least-degree condition: every apolar coefficient vector in every degree `d<r` is zero. These are precisely the hypotheses of audited `quotientMomentFunctional_frobenius`; global Frobenius is **derived**, not postulated. The audited `localCRT_hankel_of_apolar` already gives every zero-based Hankel coordinate as a sum of local product evaluations, and crucially uses all moments through `D`.

Let `S=g.roots.toFinset` and `ℓ_α=g.roots.count α>0` for `α∈S`. The audited root gate proves `∑_{α∈S}ℓ_α=r` and retains all repeated roots. The audited complex-algebra CRT map is

\[
 E:\operatorname{AdjoinRoot}(g)\simeq_{\mathbb C}
   \prod_{\alpha\in S}\operatorname{LocalTruncated}(\ell_\alpha),
 \qquad E(\bar X)_\alpha=\alpha+z_\alpha.
\]

For each `α`, the audited supported `Λ_α=localCRTComponent(g,Λ,α)` inherits **genuine local Frobenius** from the derived global Frobenius. This justifies applying audited `local_fourier_mode_coordinates` to **every** factor, including `ℓ_α>n`.

## Local nodes and exact finite sum

For each `α∈S`, define the positive integer

\[
 N_\alpha=(m-1)(\ell_\alpha-1)+1.
\]

Audited `local_fourier_mode_coordinates(m,n,ℓ_α,α,Λ_α)` yields witnesses `w_α∈LocalTruncated(ℓ_α)` and a primitive `N_α`-th root `ζ_α∈ℂ`, satisfying the exact local Frobenius root equation. Choose these witnesses **per root** without any genericity or distinctness of nodes. For `j:Fin N_α`, set

\[
 c_{\alpha,j}=N_\alpha^{-1}
    \big((\zeta_\alpha^j)^{\ell_\alpha-1}\big)^{-1},
 \qquad
 v_{\alpha,j}(i)=
   \operatorname{localModeFourierVector}
     (m,n,\ell_\alpha,\alpha,w_\alpha,\zeta_\alpha,j,i),
 \quad i:Fin n.
\]

There is no conjugation, binomial, multinomial, or mode-dependent factor. The same vector `v_{α,j}` appears in all `m` modes. Let the finite node type be the dependent sum

\[
 J=\sum_{\alpha:S}\operatorname{Fin}(N_\alpha).
\]

The first theorem should prove, for **every** `i:Fin m→Fin n`, the exact equality

\[
 (\operatorname{Hankel}h)_i
  =\sum_{(\alpha,j)\in J}c_{\alpha,j}
       \prod_{k:Fin m}v_{\alpha,j}(i_k). \tag{GF}
\]

This follows by applying the local Fourier identity to each summand in audited `localCRT_hankel_of_apolar` and reindexing `∑_α∑_{j:Fin N_α}` as a sum over `J`. The proof must not replace the local factor by evaluation at `α`, because the nilpotent derivatives are essential when `ℓ_α>1`.

## Count and frozen-width boundary

The dependent node type has exact cardinal

\[
 |J|=\sum_{\alpha:S}N_\alpha
      =(m-1)r-(m-2)|S|. \tag{COUNT}
\]

The second equality uses only `ℓ_α≥1` and `∑ℓ_α=r`; there is no assumption that roots are simple. It is a natural-number equality with the subtraction shown to be nonnegative. Reindex `J` by an actual equivalence with `Fin |J|`, not by an assumed cardinal identification, and use (GF) to construct the **frozen** `SymmetricWidth (Hankel h) |J|`. With (COUNT), the normalized-chart width has the exact displayed numerical value. Extra zero padding then permits any larger width, if needed later.

## Endpoint checks

- `r=1`: exactly one root with `ℓ=1`; `N_α=1`, the CRT algebra is one complex factor, and the construction has one symmetric node.
- One repeated root with `ℓ=r` gives `N=(m−1)(r−1)+1`, even when `r>n`; nilpotent components remain present.
- Mixed roots, such as multiplicities `3` and `2`, give `N=((m−1)·2+1)+((m−1)·1+1)=(m−1)·5−(m−2)·2`.
- `ℓ=1` forces the character exponent `ℓ−1=0`; the primitive first-root case is covered by the audited local theorem.
- `m=3`, `n=2`, and `r=D` require no separate cutoff or denominator convention. All indices are the frozen zero-based `Fin n` indices.
- A balanced apolar kernel may contain several least forms. This construction applies to **each chosen** normalized monic `g`; neither its root count nor its decomposition is assumed unique.
- `h=0` is outside the least-apolar/Frobenius route; the zero tensor must be handled separately in the full Target proof. Empty root support does not arise here because `r≥1` and `g` is monic.

## Proposed narrow Lean boundaries

1. **Local witness family and dependent-sum identity:** derive `hFrob_α` from audited global and local Frobenius theorems, choose `w_α,ζ_α` from audited `local_fourier_mode_coordinates`, and prove (GF) with exact `Sigma` node type. This gate may first expose a conditional theorem taking the genuinely proved local Frobenius family, followed by a corollary discharging it from the least-apolar hypotheses.
2. **Finite count and width:** prove `Fintype.card J=∑N_α` and (COUNT), then explicitly reindex (GF) to `Fin |J|` and construct `NLA.Statements.TR14.SymmetricWidth`. Keep all `m,n,r` hypotheses and the original zero-based tensor unchanged.
3. Freeze each module source, direct pinned build and LeanCert kernel checks, then separate imported mathematical/signature audit before aggregate import. No sorry, custom axiom, approximation, root genericity, or target weakening.

## Explicit remaining scope

The audited GL₂ chart normalization handles any nonzero original least homogeneous apolar form, including a root at infinity, and width transport can move a normalized decomposition back to the original tensor. However, **no audited theorem yet proves that the original chosen form's projective root multiset, with multiplicities, corresponds to the affine root multiset of this chart polynomial**. Thus (COUNT) is presently a normalized-chart count. The projective correspondence is required before identifying `|S|` with the `s` in canonical solution.tex for an original-coordinate numerical bound. The second symmetric upper construction, ordinary lower bounds, and all-width equivalence remain open.

## Exact source locks

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| `lean-statements/NLA/Proofs/TR14/FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| `lean-statements/NLA/Proofs/TR14/LocalFourierMode.lean` | `ab77987b8b5448ef24f59ca6c49a2598011f3b13babda48ca9cb09febe2c6626` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTRootData.lean` | `96d8d86b6e15c024978d44b78aa525dc0cbb1231fd09d274c1c0c32242c9a263` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTAlgebra.lean` | `50494ead881bed5784f24edd67bd6f954043dfd97c08202338a063f312c6c09b` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTFunctional.lean` | `fcd470c3f9b05673aa9dee6ef242c15b1b6665eafdc88b06881beebaca9582aa` |
| `lean-statements/NLA/Proofs/TR14/LocalCRTMoments.lean` | `5b429dc43ff5aed6602524c41646f76018f25cd5ea2755ae9d9c132382ee52fa` |
| Approved `LOCAL_CRT_TRANSFER_PRE_REVIEW.md` | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |

An independent mathematical review must approve this exact frozen text before Lean implementation. Changed bytes reopen that review. Canonical problem ID, README target, and frozen Lean Target remain unchanged.
