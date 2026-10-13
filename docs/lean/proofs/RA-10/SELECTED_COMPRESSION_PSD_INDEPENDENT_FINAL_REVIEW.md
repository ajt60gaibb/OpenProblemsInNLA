# RA-10 actual selected compression PSD: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact quadratic equality and frozen PSD conclusion; ordered spectral existence remains open.

The frozen source `SelectedCompressionPSD.lean` has SHA-256 `ad69432066d88ff06bbdc68c1841498c4355eb5569cbb5c976745b98f90b9222`. I checked it against the independently approved selected-compression precontract, frozen RA-10 `PositiveSemidefinite`, audited source spectral-PSD result, and actual `P=selectedProjection k QAhat`. It proves the exact finite-index identity `xᵀ(PAP)x=(Px)ᵀA(Px)` using `Pᵀ=P`; its `mulVec` uses the original matrix order. The second theorem proves **both** frozen PSD conjuncts for the actual `C=PAP`: symmetry and nonnegative quadratic form for every real vector. It uses the supplied decomposition of `A` and retains independently supplied `QAhat`, including ties, zeros, empty dimension, and out-of-range `k`. No statement of an ordered decomposition of `C` is smuggled in. The first exact signature retains the pre-reviewed `hAhat` binder although symmetry of `P` is algebraic, so Lean emits a benign unused-binder warning.

An independent imported audit at `/private/tmp/ra10-selected-compression-psd-independent-audit.lean`, SHA-256 `9c60c765598be3bd35240bfcc7d38aca1702e3afbf292fddc48c82df35f2e920`, elaborated both exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The ordered `hC` existence bridge, compression eigenvalue comparison, nuclear ideal bound, Lemma 2, integral transfer, and full RA-10 Target remain open.
