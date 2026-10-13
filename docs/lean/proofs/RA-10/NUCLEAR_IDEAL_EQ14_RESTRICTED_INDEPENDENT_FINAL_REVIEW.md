# RA-10 Equation (14) restricted ridge nuclear inequality: independent final review

**Disposition:** approved for aggregate import as the exact source Equation (14) nuclear inequality for the selected compression. The general integral transfer and full RA-10 Target remain open.

I independently inspected `NuclearIdealEq14Restricted.lean` at SHA-256 `2e06fb9cb21f3f556b619a1de3aa7fcef0a077b5bb9df8dab4fb4f406e5e289b` against the approved Equation (14) precontract, canonical source, and frozen RA-10 statement. The public theorem is exactly the preapproved `matchedLeading_ridge_nuclear_le`: `1≤k<n`, `j.val+1=k`, actual `C=PAP`, supplied ordered decompositions for `A`, `Ahat`, and `C`, exact ridge atom `t/(s+t)`, and coefficient `1/(s+a_j)` multiplying the **original frozen** `NuclearNorm (B₀−C)`. There is no extra positive-tail, commutativity, gap, or rank premise.

The proof composes the previously kernel-proved **exact** selected-resolvent nuclear equality with the independently audited coefficient-one product estimate. The literal order `P*RB*P`, `B₀−C`, `RC`, factor `s`, and cancellation remain intact. It proves the source restricted ridge difference bound, not a full operator-monotone transfer or the final Target.

Separate imported audit `/private/tmp/ra10-eq14-restricted-independent-audit.lean` at SHA-256 `34cb113e1156474670e33a3cd84d87d66232e10708bd2a5baf469a633e08eb06` restated the full public signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
