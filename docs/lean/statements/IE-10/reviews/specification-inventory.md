# IE-10 independent specification review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVE** before implementation.

The complete canonical README and ORIGINAL snapshot agree byte for byte. The target preserves universal n>=3 and 2<=k<n, two positive real constants chosen before all inputs, the real exponent and the closed success threshold at exactly 99/100. It does not substitute the stronger expectation estimate, selected constants or simultaneous-in-k consequence.

The cyclic matrix maps e_j to e_(j+1 mod n) in the stated orientation. The concrete 2n independent standard real Gaussians form a radially symmetric complex vector; normalization produces the uniform complex unit-sphere distribution. Their common scale relative to variance-one complex Gaussians cancels. The null zero draw is assigned e_0. Neither a real-sphere start nor an independent Haar subspace is introduced.

The deterministic Gram–Schmidt recursion uses conjugation on the first inner-product argument and the first k cyclic Krylov vectors. Every residual must be nonzero for success; failed residuals produce infinite condition number, so rank failure cannot count as a good compression. Fourier coordinates with distinct cyclic eigenvalues and almost-sure nonzero Gaussian coordinates give the stated almost-sure rank correspondence. Basis invariance is the genuine unitary similarity of the compression and its diagonalizers.

The diagonalizer set quantifies all invertible complex V and diagonal complex D with exact H=VDV^-1. It uses actual Euclidean operator norms. Its infimum is taken in ENNReal, where the empty infimum is infinity; nondiagonalizable H therefore fail any finite threshold. No minimizing diagonalizer is presumed to exist. The optional all-delta strict approximation formulation is equivalent to the weak finite-threshold infimum comparison and forces nonemptiness.

The finite-threshold event is measurable in this concrete model: finite piecewise Gram–Schmidt and the norm/diagonalization constraints admit real semialgebraic descriptions, and the quantifiers in the delta formulation are finite-dimensional real quantifiers. There is no nonmeasurable eigenbasis oracle. This justifies the proposed probability mathematically; it does not claim a completed Lean measurability theorem.

The cited source section was inspected for the normalized Gaussian and Krylov rank correspondence. Repeated spectra, defective compressions, exceptional starts, k=2 and k=n-1 remain included. Defining the concrete helpers suffices to state the proposition; none of the representation facts or final probability claims may be introduced as target axioms.

This approves exact specification correspondence and the concrete proposed model. It is not a proof of a resolution, a formal verification of the model-correspondence lemmas, compilation evidence, external human review or a Linux Comparator run. Every actual implemented definition requires a later independent Lean-boundary review.

## Reviewed input hashes

- `eigenvalues-and-inverse-problems/IE-10/README.md`: `61c9f5e820b4201e6b34e55cd43e3b65bc0e746dcdef6551ccfe50602ebe644a`
- `docs/lean/statements/IE-10/NUMERICAL_TARGETS.md`: `eec19ed42d3b851c634f3d775533002b4f9499a0e00f1ccd2a6d312e40529e7d`
- `docs/lean/statements/IE-10/ORIGINAL.md`: `61c9f5e820b4201e6b34e55cd43e3b65bc0e746dcdef6551ccfe50602ebe644a`
- `docs/lean/statements/IE-10/source-lock.json`: `e59ebef497522e57498b6cd6612e9f418fd3a51565cdb4a9af0dcc70b00305c9`
