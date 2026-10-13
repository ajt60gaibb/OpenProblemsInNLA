# RA-10 PSD nuclear norm equals trace: independent final review

**Disposition:** approved for aggregate import as the first exact Equation (8) block-accounting gate. Orthogonal-block additivity, Equation (8), and the full Target remain open.

I independently inspected `NuclearNormPSDTrace.lean` at SHA-256 `176e53e8f0f7b212631ec37ea00bd7d945f047beed2e77b0ce2eb9bc9771fa67` against the RA-10 source, unchanged frozen all-singular-value `NuclearNorm`, and the approved Equation (8) precontract. Its exact public theorem quantifies over every real square size and takes the actual Mathlib `Matrix.PosSemidef Y` premise; it asserts `NuclearNorm Y = Matrix.trace Y` with no rank or invertibility restriction. The theorem does not make this identification for arbitrary matrices.

For one direction the independently audited orthogonal trace upper bound is applied at `U=I`. For the other, the audited trace-attainment theorem supplies an orthogonal `U`. The proof uses positivity of `(I−U)ᵀY(I−U)` to show `trace(UᵀY)≤trace Y`: cyclicity gives `trace(UᵀYU)=trace Y`, symmetry gives `trace(YU)=trace(UᵀY)`, and the expanded nonnegative trace has the exact factor two. These identities remain valid for zero and singular PSD matrices and `Fin 0`. No spectral eigenvalue sum or numerical approximation is assumed.

Separate imported audit `/private/tmp/ra10-nuclear-psd-trace-independent-audit.lean` at SHA-256 `9a90784393edd3dcacfa43fce3589800ec589eede107f783ba3a76688b6c7e97` restated the full signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
