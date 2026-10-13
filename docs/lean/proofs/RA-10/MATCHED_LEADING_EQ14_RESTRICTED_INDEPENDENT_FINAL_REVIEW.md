# RA-10 actual-compression Equation (14): independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact restricted resolvent and nuclear-norm equalities; the nuclear inequality remains open.

The frozen source `MatchedLeadingEq14Restricted.lean` has SHA-256 `fa51611236471f41313689afaf6853a7b9c8b3ad51aae5c775819802297c2dd9`. I checked it against the independently approved Equation (14) precontract and original RA-10 source. Its `hC` is a supplied ordered PSD decomposition of **the actual** `C=PAP`, where `P=selectedProjection k QAhat` and `B₀` uses the source selected basis. The first theorem instantiates the audited right-resolvent identity and the audited support insertion, retaining `FunctionTruncation k (ridgeAtom s)`, the subtraction sign, scalar `s`, and exact noncommutative product `(P RB P)(B₀−C)RC`. The second theorem applies the frozen singular-value `NuclearNorm` to that matrix equality. It is equality by congruence, with no norm inequality or hidden replacement by the Euclidean operator norm. The selected and compression bases remain independently supplied, including ties and zero eigenvalues.

An independent imported audit at `/private/tmp/ra10-matched-leading-eq14-restricted-independent-audit.lean`, SHA-256 `05f25a28d045e228517c1411359e19a40d41701a85a48c2fa1c0733049b0f5cd`, elaborated both exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Existence of the compression decomposition, nuclear ideal inequality and numerical `1/(s+c)` bound, Lemma 2, integral transfer, and full RA-10 Target remain open.
