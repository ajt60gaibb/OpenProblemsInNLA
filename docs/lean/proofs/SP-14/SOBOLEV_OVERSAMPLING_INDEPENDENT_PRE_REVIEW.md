# SP-14 Sobolev oversampling: independent mathematical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen abstract-operator contract for Lean implementation. This review does not establish the concrete Sobolev-space instantiation, the required bounds for the actual background operator, or `NLA.Statements.SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `SOBOLEV_OVERSAMPLING_PRE_REVIEW.md` | `f6cfeb341ad824119d4c0166c9f9ebac4409231112d0f0b338f4e830aa08cbe0` |
| Canonical `counterexample.tex`, Lemma “Oversampling from two Sobolev bounds” | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separately audited `BaseJetRealSolve.lean` | `928d76ed84d4310e5feafa53c13bbf78490208ae5efafaca169f0556d6100dbe` |

## Exact checks

- The source assumes an isomorphism on both `H^s` and `H^(s+τ)` with compatible inverses. Writing these as `A_s,B_s,A_r,B_r`, together with the inclusion and finite-band lift, gives the exact identity `B_s P_h = ι B_r L_h`. The contract explicitly requires this compatibility. It cannot be inferred from separate inverse bounds alone.
- On the source's coefficient convention, `P_n` retains precisely degrees `< n`. Thus the tail begins at degree `q`, with Sobolev weight at least `(q+1)^τ`, while retained degrees have weight at most `h^τ`. The two displayed estimates reproduce the source's constants, including the denominator `q+1`; replacing these with unspecified norm bounds would lose the numerical claim.
- For `E=P_h A_s (I-P_q) B_s P_h`, the lift identity and the two estimates give `‖E y‖_s ≤ M_s (q+1)^(-τ) K_r h^τ ‖P_h y‖_s ≤ ε‖y‖_s`. The product identity `h^τ(q+1)^(-τ)=(h/(q+1))^τ` holds at `h=0` since `τ>0`. The strict `ε<1` permits the Banach-algebra Neumann inverse and the exact bound `‖(I-E)⁻¹‖≤(1-ε)⁻¹`.
- The operator order is correct: `P_h A_s P_q B_s P_h=P_h-E=P_h(I-E)`, using `A_s B_s=I`, `P_h²=P_h`, and `P_hE=E`. Multiplying by `(I-E)⁻¹` on the right proves `P_h A_s P_q R=P_h` for the proposed `R=P_qB_sP_h(I-E)⁻¹`. `P_q²=P_q` proves `P_qR=R`; projection and inverse bounds give `‖R‖≤K_s/(1-ε)`.
- At `h=0`, the finite-band estimate forces `L_0=0` and `ιL_0=P_0=0`, so `E=R=0`; the empty-target identity is valid. At `q=h=1,A_s=I`, `E=0,R=P_1`. For the contract's rational two-dimensional check, `A=[[1,1/4],[1/4,1]]` gives `E=diag(-1/15,0)` and `R=P_1`; this independently checks the sign and composition order.

The abstract theorem must return all five claims about the **displayed** `E` and `R`, with the norm bound referring to the full operator on `H_s`. It may use a single explicit norm bound for `P_h` and `P_q` or derive both from the projection family. The concrete coefficient-sequence spaces, literal truncation, and weighted estimates must remain separate named Lean obligations. In particular, the abstract algebra must not be described as proving compatible inverse bounds for the source's `𝒜_g` or the full negative SP-14 target. A completed Lean source needs a new exact-statement, proof-escape, and imported LeanCert kernel audit before aggregate import.
