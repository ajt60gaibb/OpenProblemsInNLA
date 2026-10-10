# RA-10 positive eigenvectors of the actual compression: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact positive-eigenvector support helper; the eigenvalue comparison remains open.

The frozen source `SelectedCompressionEigenvalue.lean` has SHA-256 `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13`. I checked its public signature against the independently approved min-max precontract. It derives the supplied C-basis column eigenvector equation from all four frozen ordered spectral conjuncts, retains the exact `C=PAP` with `P=selectedProjection k QAhat`, and uses the already proved `P²=P` to show `PC=C`. If the corresponding eigenvalue is strictly positive, cancellation in `λ(Pv)=λv` proves `Pv=v`. This is the actual selected range, for every dimension and index, without a spectral gap or an extra support premise.

The independent imported exact-signature audit `/private/tmp/ra10-positive-eigenvector-supported-independent-audit.lean`, SHA-256 `7d1a160887726576c772d1ab84d2282b6e8f48a8c53b869e60f5cd5d0cbcf93c`, passed pinned LeanCert kernel and reported only `propext`, `Classical.choice`, and `Quot.sound`. The subspace intersection, coefficient-one compression eigenvalue bound, nuclear inequality, and full RA-10 Target remain open.
