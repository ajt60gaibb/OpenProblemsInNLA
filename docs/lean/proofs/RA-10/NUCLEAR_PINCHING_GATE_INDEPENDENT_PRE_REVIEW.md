# RA-10 nuclear triangle and pinching: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact mathematical gate for Lean implementation, with no theorem credited until kernel checked.

I reviewed `NUCLEAR_PINCHING_GATE_PRE_REVIEW.md` at SHA-256 `23d850db3f312e04a30d732e1e9f030f04b80f5c7eff1584c4711a3aa435ffa1` against the locked RA-10 solution's Equations (8)–(9) and the frozen `NuclearNorm`. The norm is the finite sum of the actual `Matrix.toEuclideanLin` singular values over all `Fin n`, including zero values and `n=0`. The proposed triangle, real homogeneity, and two-sided orthogonal conjugation invariance have no symmetry or PSD premise on `M`; each requires a genuine kernel proof from that definition. The proposed dual characterization, if used, must also be proved, not assumed.

For `Pᵀ=P` and `P²=P`, `U=2P−I` satisfies `Uᵀ=U` and `U²=I`. Expanding both sides gives `PMP+(I−P)M(I−P)=(M+UMU)/2`, with the same multiplication order as the source's two-block pinching. Triangle, homogeneity at `1/2`, and orthogonal invariance then give the exact coefficient `1`, independent of dimension. The identity also holds at `n=0`; it does not choose a favorable basis, assume a spectral gap, or restrict `M` to PSD. The selected-projection bridge from frozen `QAhat` remains separate.

Approval covers the source-locked signatures and mathematics, not an implementation. If the pinned library lacks the needed singular-value theorem, report the gate open instead of importing an axiom or weakening the frozen target. Every completed source module needs a separate frozen-source, exact-signature, LeanCert kernel and transitive-axiom audit before aggregate import.
