# TR-14 local Fourier symmetric upper bound: exact pre-implementation contract

**Author:** `/root/tr14_frob_review` (AI agent), 10 October 2026. **Status:** frozen mathematical and proposed Lean contract for an independent review **before** implementation. This covers only the local-interpolation upper construction in canonical `solution.tex` §3. It does not prove the second upper bound, the arbitrary ordinary lower bound, or `NLA.Statements.TR14.Target`.

## Frozen target context and precise conditional claim

The unchanged TR-14 target quantifies over every `m≥3`, `n≥2`, `h : Fin (m*(n-1)+1) → ℂ`, and natural width `r`. Put `q=n-1≥1` and `D=mq≥3`. For **nonzero** `h`, the audited least-apolar theorem selects `1≤r₀≤⌊D/2⌋+1` and a nonzero homogeneous degree-`r₀` apolar form. The audited chart-normalization and width-transport modules permit a choice of `z∈ℂ`, transformed moments `h'=transformedMoments z h≠0`, and a monic affine polynomial `g` of **exact degree** `r₀` giving all frozen apolar equations. The audited quotient theorem supplies `A=ℂ[t]/(g)` and `λ:A→ₗ[ℂ]ℂ` with `λ([t^j])=h'_j` for **every** `0≤j≤D`; the audited Frobenius theorem supplies nondegeneracy of `(a,b)↦λ(ab)`.

This contract's eventual public consequence is the following exact upper bound, where `s` is the number of **distinct projective roots** of the originally chosen homogeneous apolar form, counted without multiplicity:

\[
  \operatorname{SymmetricWidth}(\operatorname{Hankel}(h),R_{\rm loc}),
  \qquad
  R_{\rm loc}=(m-1)r₀-(m-2)s.
\]

After normalization all roots of `g` are finite, so its distinct affine roots have the same `s` and the same multiplicities as the original projective roots. Returning from `h'` to `h` uses the **proved** reverse direction of `chart_widths_iff`, with the same scalar and inverse-transpose mode factor in every mode. No root-at-infinity exclusion is allowed in the original-coordinate conclusion. For `h=0`, use the audited width-zero and padding lemmas separately; no `r₀`, `g`, or root count is assigned to zero moments. The bound is an exact-width witness with `R_loc` summands, including any summands whose coefficient happens to vanish.

## Factorization and local Frobenius data

The fundamental theorem of algebra yields **distinct** `α_a∈ℂ`, indexed by a finite type of cardinality `s≥1`, and **positive** multiplicities `ℓ_a≥1` such that

\[
g(t)=\prod_{a=1}^{s}(t-α_a)^{\ell_a},\qquad
\sum_a\ell_a=r₀.
\]

Distinctness gives pairwise coprime factors and a complex-algebra CRT equivalence preserving the residue of `t`:

\[
A\simeq\prod_a A_a,
\qquad A_a=\mathbb C[z_a]/(z_a^{\ell_a}),
\qquad z_a=t-α_a.
\]

Define `λ_a` by applying `λ` to the CRT element supported in the `a`th factor. Then `λ(x)=∑_a λ_a(x_a)` **for every** `x∈A`, and each `λ_a` is Frobenius: a nonzero local radical element, embedded with zero other coordinates, would be a nonzero global radical element. This requires the actual CRT isomorphism and preservation of multiplication; it cannot be postulated as a new assumption of the frozen Target.

Represent each local class by its unique polynomial of degree `<ℓ_a`. There is a **unique** local class `u_a=∑_{j=0}^{ℓ_a-1}u_{a,j}z_a^j` satisfying

\[
  λ_a(f)=[z_a^{\ell_a-1}](u_af)
  \quad\text{for every }f∈A_a,
  \qquad
  u_{a,j}=λ_a(z_a^{\ell_a-1-j}).
\]

In particular `u_{a,0}=λ_a(z_a^{ℓ_a-1})≠0`: if it vanished, the nonzero class `z_a^{ℓ_a-1}` would pair to zero with every local class. This includes `ℓ_a=1`, where `z_a^0=1` and `λ_a(1)≠0`. Thus `u_a` is a unit. Because `m≥3` and the field is `ℂ`, choose an `m`th root of `u_{a,0}`, then use the **finite** nilpotent binomial expansion in the ideal `(z_a)` to obtain a local unit `w_a` with `w_a^m=u_a`. No analytic convergence, numerical root approximation, or infinite series is involved.

## Exact Fourier cutoff and symmetric factors

For each `a`, set

\[
  N_a=(m-1)(\ell_a-1)+1\ge1.
\]

Let `μ_{N_a}={ζ∈ℂ:ζ^{N_a}=1}`; it has exactly `N_a` distinct elements, all nonzero. For any `m` polynomials `f_k(z)` of degree `<ℓ_a`, the unreduced product has degree at most `m(ℓ_a-1)`. Character orthogonality gives the **exact** identity

\[
 [z^{\ell_a-1}]\prod_{k=1}^{m}f_k(z)
 =\frac1{N_a}\sum_{ζ∈μ_{N_a}}
       (ζ^{\ell_a-1})^{-1}\prod_{k=1}^{m}f_k(ζ).
\]

The only integer in `[0,m(ℓ_a-1)]` congruent to `ℓ_a-1` modulo `N_a` is `ℓ_a-1` itself: the next is `m(ℓ_a-1)+1`, one above the maximum; the previous is negative. At `ℓ_a=1`, `N_a=1`, the degree range is `{0}`, and the formula has one node `ζ=1`. This endpoint is required, not a limiting argument. The character factor is ordinary complex inversion, **never** conjugation of tensor coordinates. For every `m≥3`, all denominators `m` and `N_a` are nonzero in `ℂ`.

For a mode coefficient vector `v:Fin n→ℂ`, use the exact zero-based affine polynomial `p_v(t)=∑_{i=0}^{q}v_i t^i`, with **no binomial factors**. Let `f_{a,v}(z)` be the unique degree-`<ℓ_a` representative of the local class `w_a·p_v(α_a+z)`. Define the complex-linear mode functional

\[
 F_{a,ζ}(v)=f_{a,v}(ζ).
\]

This evaluates the **polynomial representative**, not a quotient class at `ζ` (evaluation at a nonnilpotent `ζ` is generally not well-defined on `A_a`). Because taking a representative, multiplication by fixed `w_a`, and evaluation are linear, `F_{a,ζ}` is linear in `v`. Its coordinate vector is `V_{a,ζ}(i)=F_{a,ζ}(e_i)` for `0≤i≤q`, so `F_{a,ζ}(v)=∑_iV_{a,ζ}(i)v_i`.

For arbitrary `m` mode vectors `v_k`, all-moment matching through `D=mq` and the audited zero-based Hankel pairing give

\[
 H_{h'}(v_1,\ldots,v_m)
 =λ\!\left(\prod_k[p_{v_k}]\right)
 =\sum_aλ_a\!\left(\prod_k[p_{v_k}]_a\right)
 =\sum_a\sum_{ζ∈μ_{N_a}}
      c_{a,ζ}\prod_kF_{a,ζ}(v_k),
 \quad
 c_{a,ζ}=N_a^{-1}(ζ^{\ell_a-1})^{-1}.
\]

The third equality uses `w_a^m=u_a`. Taking all `v_k=e_{i_k}` yields the frozen coordinate identity

\[
 (\operatorname{Hankel}h')_{i_1\ldots i_m}
  =\sum_{a,ζ} c_{a,ζ}\prod_{k=1}^{m}V_{a,ζ}(i_k).
\]

The **same** `V_{a,ζ}` occurs in every mode. Reindex the disjoint union of root-of-unity sets to `Fin R_loc` using

\[
 \sum_aN_a
 =\sum_a\bigl((m-1)(\ell_a-1)+1\bigr)
 =(m-1)r₀-(m-2)s.
\]

This is a witness for the frozen `SymmetricWidth`, not merely a Vandermonde or border-rank statement. It works when `r₀>n` because local reduction is performed in `A_a`; no assumption `ℓ_a≤n` is made. For the balanced endpoint `D=2r₀-2`, the chosen minimal apolar form need not be unique, but this construction applies to **any** nonzero chosen form; its bound may exceed `r₀`, while the source's separate binary upper construction attains the `r₀` branch. Do not infer the full exact-rank formula from this local bound alone.

## Proposed Lean proof boundaries and endpoints

These are signature sketches, not compiled Lean. Ellipses denote exact type transports and proved degree bounds, never new mathematical assumptions in `Target`.

1. **CRT data:** from a monic `g` of exact positive degree over `ℂ`, construct distinct roots, positive multiplicities, their sum `r₀`, a finite-product algebra equivalence `A≃ₐ[ℂ]∏A_a`, and local Frobenius functionals whose sum is `λ`. Keep `t̄` mapped to `(α_a+z_a)_a`.
2. **Local top coefficient:** prove the displayed unique `u_a`, `u_{a,0}≠0`, and a local `w_a` with `w_a^m=u_a` for every `ℓ_a≥1`; prove all finite representative operations have the claimed degrees and are linear.
3. **Fourier lemma:** for every `m≥3`, `ℓ≥1`, and `m` polynomials of degree `<ℓ`, prove the displayed coefficient identity with exactly `N=(m-1)(ℓ-1)+1` roots; explicitly handle `ℓ=1` and the endpoint exponents `0` and `m(ℓ-1)`.
4. **Moment-to-quotient bridge:** prove, from the already audited all-moment identity and exact zero-based mode expansion, `H_{h'}(v_1,…,v_m)=λ(∏[p_{v_k}])` for every `v_k`. This is a distinct obligation; equality only for individual moments below `r₀` is insufficient.
5. **Local symmetric decomposition:** construct `F_{a,ζ}`, `c_{a,ζ}`, and `V_{a,ζ}`; prove the frozen coordinate equation and a `SymmetricWidth(Hankel h',R_loc)` witness. Reindex by the **proved** node count; zero coefficients may remain in an exact-width witness.
6. **Original-coordinate corollary:** use the audited chart normalization and `chart_widths_iff` to obtain `SymmetricWidth(Hankel h,R_loc)` for the original `h`. Preserve `m≥3`, `n≥2`, root-at-infinity and all multiplicity cases. The finite `n=q+1` type transport must be proved explicitly.

Every eventual Lean source must be separately frozen and independently audited for exact statement, imported LeanCert kernel trust, and transitive axioms. A conditional local Fourier theorem is allowed as an intermediate theorem only if its factorization/CRT hypotheses are themselves subsequently proved from the canonical nonzero `h`; they must not be added to the final Target.

## Independent self-check and source locks

I checked the arithmetic at `m=3,ℓ=1` (`N=1`, only degree `0`), `m=3,ℓ=2` (`N=3`, product degrees `0..3`, selected degree `1`, next congruent degree `4`), and `m=3,ℓ=3` (`N=5`, degrees `0..6`, selected degree `2`, next `7`). The general next-congruent calculation above proves all `m≥3,ℓ≥1`. The representation `u_{a,j}=λ_a(z^{ℓ-1-j})` was checked by multiplying bases and selecting only total degree `ℓ-1`. The count identity was checked algebraically using `∑ℓ_a=r₀` and the exact number `s` of distinct factors. The Fourier step uses representatives before evaluation and therefore does not confuse quotient classes with complex points.

| Input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` (§§2–3) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Approved `EXACT_PROOF_PRE_REVIEW.md` | `abd73514c57e2d8c5f6a2709273a43ad282c854c8647e99855492f23052a6698` |
| Independent approval `EXACT_PROOF_INDEPENDENT_PRE_REVIEW.md` | `35f0045858ee95aead041fc86cce52dd2f061fcb804f749491762f9f69fbfe53` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |
| Audited `FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| Audited `GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |
| Audited `GL2HankelMode.lean` | `5b700ce0fbd05cfa39f047830b6455dc64cc361acfe3218f667d2af9f09e02c2` |
| Audited `GL2WidthTransport.lean` | `5a50bb7984b3a9dd034faae43ab088f4ec10880ce37128cad9afd79af1a528a4` |
| Frozen `GL2MiddleRankTransport.lean` | `00d2b76e502b2ddc9f06b9cd0379d39d646399fc15d826f7d549dfc63a2e7b13` |

An independent mathematical review of **this exact document** is required before local-Fourier Lean implementation. Changed bytes reopen that review. The unchanged full TR-14 Target remains open.
