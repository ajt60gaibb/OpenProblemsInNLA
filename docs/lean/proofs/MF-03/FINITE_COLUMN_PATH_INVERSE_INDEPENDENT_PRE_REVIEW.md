# MF-03 literal path and column-system inverses: independent pre-review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact two inverse contracts for staged Lean implementation; neither inverse is yet claimed.

I checked `FINITE_COLUMN_PATH_INVERSE_PRE_REVIEW.md` at SHA-256 `48a482be2235b48f96aad1e4f2f4293f4aa02367e74abc0a1cc179d717f75b2f` against the unchanged MF-03 source, frozen `FiniteValidPath`, `finiteAdvanceLabels`, `finitePathAtCut`, the audited actual-label column system, and the exact reconstructed path. All source hashes match. Both maps retain the original omitted-row start, terminal tuple, descending zero-based factor order, and unchanged `FiniteColumnSystem` type.

For `D→path→D`, the induction on the auxiliary chain length recovers precisely `{k∈D.labels p:k<n}` at every coordinate. The first length-`n+1` transition has label `n` and advances exactly when `n` belongs to the original set; its tail cannot already contain `n`. At `n=N`, every original label is `<N`, yielding equality of all actual finite sets and therefore equality of the full structure, not only its cardinalities.

For `path→D→path`, `finitePathAtCut` at the first non-top cut is exactly the first intermediate tuple. Agreement at every cut determines all later tuples by induction, with proposition-valued validity proofs irrelevant. The frozen suffix-position theorem identifies an existing path's every cut with the constructor's `P_q`; hence cut extensionality gives literal equality of chains. The argument covers empty coordinates, zero factors, and both extreme augmented shapes. It neither inserts sentinel `N` nor evaluates a weight.

Approval covers the two inverse laws and their eventual `Equiv` packaging. Each implemented stage requires a frozen source hash, direct pinned LeanCert kernel check, and independent imported exact-signature/source/axiom audit before aggregate import. Weight transport, determinant/tableau equality, and full MF-03 Target remain open.
