# SP-14 Sobolev oversampling: exact finite right-inverse pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical review before Lean source. The fixed `Target` is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Lemma “Oversampling from two Sobolev bounds” and its proof (lines 1780–1806). The separately reviewed constructive base model is `BaseJetRealSolve.lean`, frozen SHA-256 `928d76ed84d4310e5feafa53c13bbf78490208ae5efafaca169f0556d6100dbe`; it establishes no perturbed-background inverse estimate.

## Exact mathematical statement

Fix real `s`, `τ>0`, and natural `q≥h`. Let `H_s` and `H_r` represent the **same coefficient sequences** with Sobolev exponents `s` and `r=s+τ`; let `ι:H_r→H_s` be their canonical inclusion. Let `A_s,A_r` and `B_s,B_r` be compatible bounded complex-linear operators, with `A_sB_s=B_sA_s=I`, `A_rB_r=B_rA_r=I`, and `ιB_r=B_sι` (likewise `ιA_r=A_sι`). For `n≥0`, `P_n` is the exact projection onto coefficients of degree `<n`, so `P_n²=P_n` and `‖P_n‖_{H_s→H_s}≤1`. Let `L_h:H_s→H_r` be the canonical finite-band lift of `P_h`, satisfying `ιL_h=P_h`. The following are the *explicit Sobolev estimates*, not unspecified right-inverse premises:

\[
 \|(I-P_q)\iota x\|_s\le(q+1)^{-\tau}\|x\|_r,
 \qquad \|L_h y\|_r\le h^\tau\|P_hy\|_s.
\]

Assume nonnegative constants `M_s,K_s,K_r` with `‖A_s‖≤M_s`, `‖B_s‖≤K_s`, and `‖B_r‖≤K_r`, and put
\[
 \varepsilon=M_sK_r\left(\frac{h}{q+1}\right)^\tau<1.
\]
Define, in the bounded-operator algebra on `H_s`,
\[
 E=P_hA_s(I-P_q)B_sP_h,
 \qquad R=P_qB_sP_h(I-E)^{-1}.
\]
The public theorem must establish **all** of `‖E‖≤ε`, invertibility of `I-E`, `P_qR=R`, `P_hA_sP_qR=P_h`, and `‖R‖≤K_s/(1-ε)`. In particular the range of `R` has degree `<q`, and its restriction to `P_hH_s` is the explicit right inverse for `P_hA_sP_q`. This is the source's formula, not merely existence of some finite inverse.

The intended standalone Lean interface is two complete complex normed spaces `Hs Hr`, continuous linear maps `incl`, `As Ar Bs Br`, `P : ℕ → Hs →L[ℂ] Hs`, and `Lh : Hs →L[ℂ] Hr`, the above exact inverse/compatibility, projection, lift, norm and tail hypotheses, and a theorem returning the five conclusions for the explicitly defined `E` and `R`. The concrete `H^s` sequence-space instantiation must be a **separate named obligation**: it must identify `Hs/Hr` with coefficient sequences whose squared norms are `∑_{n≥0}(n+1)^{2s}|x_n|²` and `∑_{n≥0}(n+1)^{2(s+τ)}|x_n|²`, and prove that `P_n` is the literal truncation. An abstract operator theorem alone may be reported only as the source's oversampling algebra, not as completion of the actual Sobolev instantiation.

## Proof and endpoint audit

For any `y∈H_s`, compatibility and `ιL_h=P_h` give `B_sP_hy=ι B_rL_hy`. Therefore the two displayed weighted estimates yield
\[
 \|Ey\|_s\le M_s(q+1)^{-\tau}K_r h^\tau\|P_hy\|_s
 \le\varepsilon\|y\|_s.
\]
The real-power identity `h^τ(q+1)^{-τ}=(h/(q+1))^τ` uses `h≥0`, `q+1>0`; it remains valid at `h=0` because `τ>0`. The Neumann lemma yields `‖(I-E)^{-1}‖≤(1-ε)^{-1}`. Since `A_sB_s=I`, `P_h²=P_h`, and `P_hE=E`, one has `P_hA_sP_qB_sP_h=P_h-E=P_h(I-E)`; multiplication by `(I-E)^{-1}` proves the exact right-inverse identity. The projection norms prove the stated norm bound and `P_qR=R`.

At `h=0`, the concrete `P_0=0` gives `E=R=0`, `ε=0`, and the identity is the zero map. At `q=h=1`, `A_s=I` gives `E=0` and `R=P_1`; the finite right inverse is exact. For a nontrivial rational algebra check on `ℂ²`, take `h=q=1`, `P_1=diag(1,0)`, and `A=[[1,1/4],[1/4,1]]`. Its inverse is `(16/15)[[1,-1/4],[-1/4,1]]`; direct multiplication gives `E=diag(-1/15,0)`, `(I-E)^{-1}=diag(15/16,1)`, and `R=P_1`, hence `P_1AP_1R=P_1`. This checks the sign in `I-E` and the operator order independently of any Sobolev estimate.

## Scope and feasibility

This gate constructs a right inverse once compatible Sobolev inverse bounds are supplied. It does **not** prove that the actual background-dependent operator `\mathcal A_g` in Proposition “Two explicit analytic estimates would suffice locally” has those bounds, nor the forcing estimate, replacement of the limiting Jacobian by finite matrices, nonlinear contraction, norm budgets, one-sided nonextension, canonical spectral gap, or the frozen negative `Target`. Implementing the abstract operator core is bounded finite algebra plus a Neumann inverse in a Banach algebra. The actual weighted sequence-space specialization and the source's background estimates are larger analytic obligations and must remain visible; no theorem may silently rename the abstract hypotheses as already verified for `\mathcal A_g`.
