# RA-10 exact nuclear pinching contraction: independent final review

**Disposition:** approved for aggregate import as the coefficient-one two-block pinching theorem. The full source Equation (8) and RA-10 Target remain open.

I independently inspected `NuclearPinching.lean` at SHA-256 `94b0777dc73b1d23bceeda78714a5e1788d1c5ed8f677a7258401bc71b8ff033` against the source Equation (8), frozen `NuclearNorm`, and the reviewed exact pinching contract. Its public signature assumes only `Pᵀ=P` and `P²=P`, takes arbitrary real square `M` and every natural dimension, and bounds the literal frozen all-singular-value norm of `PMP+(I−P)M(I−P)` by that of `M` with coefficient one. It imposes no PSD, commutation, rank, or spectral-gap premise.

The proof uses the previously audited `U=2P−I` reflection, whose two orthogonality equations and exact matrix average identity hold in noncommutative order. The independently audited frozen triangle, homogeneity at exactly `1/2`, and two-sided orthogonal invariance yield the coefficient-one contraction. The same proof covers `P=0`, `P=I`, `n=0`, and nonsymmetric `M`; it does not silently replace the nuclear norm by the trace or operator norm.

Separate imported audit `/private/tmp/ra10-nuclear-pinching-independent-audit.lean` at SHA-256 `5ffbee632afc346a36e82f6aa5bdf561b4d883af9d40f8bf21e9484ee96de4de` restated the exact public signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom. Orthogonal-block nuclear additivity and PSD trace accounting still need separate proofs before source Equation (8) can be claimed.
