# TR-14 nonzero affine-root coordinate: independent pre-implementation review

**Disposition:** approve the sole exact public signature in `GL2_MOBIUS_EVAL_PRE_REVIEW.md` for implementation as a partial gate. It does not establish root multiplicities, the projective support count, any width equality, or the frozen Target.

I independently checked the proposal at SHA-256 `898cec630d03b57666f48f2eebb1f43d9c19eb137ce0d5bed4eea4eb2246c2c7` against the canonical TR-14 README and solution, the frozen statement, and all seven listed Lean dependency sources. Every recorded SHA-256 matches. The source changes the projective chart while retaining multiplicities; the proposed theorem isolates only the scalar nonzero-coordinate evaluation needed for that later bridge.

The audited polynomial identity states `p_z(t)=Σ_{i=0}^d g_i t^(d−i)(1+zt)^i`. For `t≠0`, the exact algebraic identity `1+zt=t(z+t⁻¹)` converts each term into `g_i t^d(z+t⁻¹)^i`, proving the proposed right side with the **ambient** degree `d`. It holds for zero and trailing coefficients, `d=0`, and all `z`; no monicity or apolarity hypothesis is required. This ambient exponent is necessary to retain the point at infinity and must not be replaced by `p.natDegree`.

The contract's degree-two check is correct: for `g=(a,b,c)`, both sides expand to `c+(b+2cz)t+(a+bz+cz²)t²`. For `z=0`, it is the degree-`d` reciprocal polynomial identity. The nonzero root correspondence `α=z+t⁻¹` follows, but multiplicity preservation and the exceptional `t=0` case remain separate obligations. Implementation must be in a new module, with pinned Lean 4.33.1/LeanCert `kernel`, followed by a separate imported exact-signature and axiom audit before aggregate import.
