# TR-14 homogeneous GL₂ chart transport: exact pre-proof contract

**Author:** /root/tr14_frob_review (AI agent), 10 October 2026. **Status:** frozen mathematical and proposed Lean contract for independent review **before** implementation. This bridges the canonical homogeneous apolar problem to the audited normalized quotient and middle catalecticant theorems. It does not prove the frozen all-width Target.

## Exact objects and orientation

For the frozen target, m≥3, n≥2, q=n−1, and D=mq. The finite chart lemma may be proved for any D≥1. Let V_d be the homogeneous binary forms of ambient degree d over ℂ, represented by coefficient vectors on Fin(d+1) in the basis X^(d−i)Y^i. A trailing zero coefficient is allowed. Define L_h on V_D by L_h(X^(D−j)Y^j)=h_j for **every** 0≤j≤D. This is an isomorphism between moment vectors and the degree-D dual; there is no binomial rescaling or conjugation.

For T∈GL₂(ℂ), use one convention throughout:

\[
\varphi_{T,d}P(X,Y)=P(T(X,Y)),\qquad
L_{h'}=L_h\circ\varphi_{T,D}^{-1},\qquad
h'_j=L_{h'}(X^{D-j}Y^j).
\]

Every φ_{T,d} is an invertible complex-linear map. It respects multiplication exactly: φ_{T,d+e}(PQ)=(φ_{T,d}P)(φ_{T,e}Q). Therefore, for **every** split d+(D−d)=D and every P∈V_d, Q∈V_{D−d},

\[
L_{h'}((\varphi_{T,d}P)(\varphi_{T,D-d}Q))=L_h(PQ).
\]

This inverse-dual orientation is compulsory. Transforming the apolar form without the moment functional, using the forward rather than inverse dual action, or conjugating coefficients would invalidate the displayed identity.

## Every apolar degree and chart normalization

For 0≤d≤D, the audited IsApolar predicate means exactly that for G=Σ_{i=0}^d g_iX^(d−i)Y^i,

\[
\sum_{i=0}^d g_i h_{i+j}=0 \qquad(0\le j\le D-d).
\]

First prove this is equivalent to ∀Q∈V_{D−d}, L_h(GQ)=0. The monomial Q=X^(D−d−j)Y^j yields each exact convolution equation, including both endpoints. Then prove the full all-degree correspondence

\[
G\in I_d(h)\iff \varphi_{T,d}G\in I_d(h'),\qquad
\varphi_{T,d}(I_d(h))=I_d(h')\quad(0\le d\le D).
\]

The canonical source defines I_d=V_d when d>D; if an all-natural-degree API is exposed, carry these full spaces too. The least-degree application needs only d≤D, but testing apolarity just at a selected r₀ or middle split is insufficient. Since φ_{T,d} is invertible, it preserves dimensions and nonzero elements. Since L_h=0 iff h=0, the inverse-dual map gives h'=0 iff h=0. Thus nonzero moments stay nonzero, and the least nonzero homogeneous apolar degree from the audited minimal_apolar_exists theorem is identical for h and h'.

For every h≠0, take its audited witness 1≤r₀≤⌊D/2⌋+1 and **any** nonzero G∈I_{r₀}(h). The original last coefficient g_{r₀} may be zero, recording a root at infinity. Prove that G(1,z)=Σ_{i=0}^{r₀}g_i z^i is a nonzero polynomial. Since ℂ is infinite, choose z with G(1,z)≠0. One explicit invertible substitution is

\[
T=\begin{pmatrix}0&1\\1&z\end{pmatrix},
\qquad \det T=-1,\qquad T(0,1)=(1,z).
\]

Then (φ_{T,r₀}G)(0,1)=G(1,z)≠0. Scale φ_{T,r₀}G by the inverse of this coefficient. The resulting G_norm∈I_{r₀}(h') has affine polynomial g_norm(t)=G_norm(1,t) monic of **exact degree r₀**. Scaling preserves nonzero apolarity, while every lower transformed kernel stays zero. This works for a root at infinity without genericity, squarefreeness, simple roots, or numerical root finding.

The zero moment vector is treated separately by the audited zero-tensor and width-zero lemmas; it is not assigned a positive least apolar degree. At the balanced endpoint D=2r₀−2, the least apolar space may have dimension two: normalize each chosen nonzero member without assuming uniqueness. At r₀=1 and the finite endpoint D=1, the same evaluation and substitution cover forms whose affine leading coefficient initially vanishes.

## Frozen Hankel tensor in all m modes

For u:Fin n→ℂ, put p_u(X,Y)=Σ_{i=0}^q u_iX^(q−i)Y^i∈V_q. The frozen zero-based tensor has the exact multilinear identity

\[
\sum_{i_1,\ldots,i_m=0}^{q}
  (\mathrm{Hankel}\ h)_{i_1,\ldots,i_m}
  \prod_{k=1}^{m}u_{k,i_k}
=L_h(p_{u_1}\cdots p_{u_m}).
\]

No multinomial coefficients appear. Let M_T:ℂ^n→ℂ^n be the invertible coefficient map of φ_{T,q}, so p_{M_Tu}=φ_{T,q}p_u. The degree-D pairing identity must yield, for **every** tuple of m mode vectors,

\[
H_{h'}(M_Tu_1,\ldots,M_Tu_m)=H_h(u_1,\ldots,u_m).
\]

The same M_T acts in all modes. In the frozen coordinate tensor convention, a decomposable factor transforms by M_T^{-T}; conversely it transforms by M_T^T. This is ordinary transpose, not conjugate transpose. Hence the chart bridge must prove, for **every** width r≥0 including empty sums, both OrdinaryWidth(Hankel h,r) iff OrdinaryWidth(Hankel h',r) and SymmetricWidth(Hankel h,r) iff SymmetricWidth(Hankel h',r). Symmetric summands use the same inverse-transpose map on every copy of their factor. These are rank-preserving chart equivalences, not equality between ordinary and symmetric widths.

For the middle catalecticant, set a=⌊D/2⌋, b=⌈D/2⌉. The degree-(a,b) pairing identity gives M_{T,a}^T C_{h'} M_{T,b}=C_h in the exact monomial bases. Both matrices are invertible, so the middle ranks agree. This middle-degree relation alone does **not** show h' has the same least apolar degree; the all-degree kernel correspondence above must precede any application of the audited normalized middle-rank theorem. No chart or monicity assumption may become an extra premise of the frozen Target.

## Proposed Lean boundaries

The signatures are mathematical API sketches. A homogeneous MvPolynomial, symmetric-power, or coefficient-function representation is acceptable if it proves these same identities. Ellipses represent only index and degree bound proofs.

    homogeneousMoment h : V D →ₗ[ℂ] ℂ
    phi (T : GL₂(ℂ)) (d : ℕ) : V d ≃ₗ[ℂ] V d
    transformedMoments (T : GL₂(ℂ)) h : Fin(D+1) → ℂ

    transformed_pairing (T) (d≤D) (P : V d) (Q : V(D−d)) :
      L_(transformedMoments T h) ((phi T d P)*(phi T (D−d) Q)) = L_h(P*Q)

    apolar_transport (T) (d≤D) (G : V d) :
      IsApolar h d G ↔ IsApolar (transformedMoments T h) d (phi T d G)

    normalize_minimal_apolar (h≠0) (G≠0) (G∈I_r₀(h)) (all lower I_d(h)=0) :
      ∃ T∈GL₂(ℂ), ∃ G_norm∈V_r₀,
        transformedMoments T h ≠ 0 ∧ G_norm∈I_r₀(transformedMoments T h) ∧
        coeff(G_norm,r₀)=1 ∧ all lower transformed kernels are zero

    hankel_mode_transport (m≥3) (n≥2) (T) (u : Fin m → Fin n → ℂ) :
      H_(transformedMoments T h) (fun k => M_T (u k)) = H_h u

    chart_widths_iff (m≥3) (n≥2) (T) (r : ℕ) :
      (OrdinaryWidth(Hankel h,r) ↔ OrdinaryWidth(Hankel h',r)) ∧
      (SymmetricWidth(Hankel h,r) ↔ SymmetricWidth(Hankel h',r))

The implementation may separate substitution, moment duality, apolar transport, normalization, and tensor transport into smaller modules. The normalized quotient/Frobenius and normalized middle-rank theorems may not be applied to arbitrary original h before these bridges are proved. Local CRT factors, balanced choice independence, symmetric upper bounds, and the arbitrary ordinary lower bound remain separate. This chart contract alone proves no full TR-14 Target.

## Source locks and review gate

| Input | SHA-256 |
| --- | --- |
| Canonical tensor-computations/TR-14/README.md | a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86 |
| Canonical tensor-computations/TR-14/solution.tex (§2) | 0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6 |
| Frozen lean-statements/NLA/Statements/TR14.lean | 515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9 |
| Audited lean-statements/NLA/Proofs/TR14/ApolarMinimal.lean | 0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9 |
| Audited lean-statements/NLA/Proofs/TR14/NormalizedQuotient.lean | 3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d |
| Audited lean-statements/NLA/Proofs/TR14/FrobeniusMinimal.lean | dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e |
| Frozen normalized lean-statements/NLA/Proofs/TR14/MiddleCatalecticant.lean | 2ddbf89822f72c4cbc5a2cd6935adbbab49239476943275ac4a5b2853be9d8a1 |
| Approved QUOTIENT_FROBENIUS_PRE_REVIEW.md | 3b8d8d1484755f149c61feb992255c6be617f659219eb0c1bf96b165c0134eea |
| Approved MIDDLE_CATALECTICANT_PRE_REVIEW.md | b72a9a0e25358fbe2b41dff423c638c03202bc367d6153cf4f08c0e1fb054981 |

An independent mathematical review of **this exact contract** is required before any chart Lean source. A frozen implementation later needs a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit. Changed contract or source bytes reopen the respective review.
