# RA-10 spectral quadratic form: independent pre-implementation review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact narrow contract `SPECTRAL_QUADRATIC_GATE_PRE_REVIEW.md` at SHA-256 `5697cd4d02a0c3fa37202fa7e9c31173e8f23f33046bc0bce1427f0b67d198fc` before Lean implementation.

I compared the proposed theorem signatures directly with the frozen `SpectralMatrix`, `OrderedPSDSpectralDecomposition`, and `PositiveSemidefinite` definitions. Expanding the literal entry `Sᵢⱼ=∑ₐλₐQᵢₐQⱼₐ`, the finite double sum rearranges to `∑ₐλₐ(∑ᵢxᵢQᵢₐ)(∑ⱼxⱼQⱼₐ)`, giving the proposed square exactly. It uses every `Fin n` eigenvalue and holds for `n=0` without a positivity or basis assumption. Real multiplication gives `Sᵢⱼ=Sⱼᵢ`; nonnegative `λₐ` makes each quadratic summand nonnegative. Replacing `S` by the supplied `A` in the frozen decomposition gives the exact frozen PSD predicate, with the **same** `A`, eigenvalues, and selected basis, even under ties or zero eigenvalues.

This approval covers only the quadratic identity and the resulting PSD implication. It does not establish any nuclear norm, spectral min-max, ridge compression, integral representation, constant-eleven transfer, or full `Target`. Freeze the Lean source for an independent exact-signature and LeanCert kernel audit after implementation.
