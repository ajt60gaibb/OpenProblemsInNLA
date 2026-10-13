# RA-10 sharp left nuclear ideal: independent final review

**Disposition:** approved for aggregate import as the exact coefficient-one left ideal inequality. The right ideal inequality, Eq. (14), and full RA-10 Target remain open.

I independently inspected `NuclearIdealLeft.lean` at SHA-256 `9a31268a63097da9711e696ee3b1a2c2b40b57b301c6590fa9f0c88bcccfa221` against the approved source contract and frozen `Statements/RA10.lean`. Its public theorem is the exact `NuclearNorm (X*Y)≤‖X‖*NuclearNorm Y` for every real square `X,Y` and natural dimension under the scoped Euclidean L2 operator norm. It unfolds the **original** nuclear norm, sums the independently audited same-index inequality over every `i:Fin n`, and factors out the unchanged coefficient-one scalar. Empty `Fin 0`, zero and tied singular values, and arbitrary nonnormal matrices are included; no rank or invertibility assumption is added.

Separate imported audit `/private/tmp/ra10-left-ideal-independent-audit.lean` at SHA-256 `3da343bff1b0e7714fa37e37081e9c0dd0d7e23743af5eceffcb1db2f6e16e0d` restated the exact public signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
