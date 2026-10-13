# RA-10 matched-leading support algebra: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact projector insertion for source Equation (14); the nuclear ideal inequality remains open.

The frozen source `MatchedLeadingSupport.lean` has SHA-256 `426403f51df54d1ffa70f839b18921da2a9b63ea265112213e8c66d2530c0c18`. I checked it against the independently approved support precontract, frozen RA-10 matrix definitions, selected-projector algebra, matched-leading decomposition, and original source Equation (14). The module uses the actual `P=selectedProjection k QAhat`, `B₀=FunctionTruncation k id eigenvaluesA QAhat`, `C=PAP`, and `D=B₀−C`. It proves `PB₀P=B₀`, `PCP=C`, and `PDP=D` from the supplied decompositions. The actual inverse `R_B₀=(sI+B₀)⁻¹` commutes with `P` because both are spectral in the same supplied `QAhat` basis. The final equality `R_B₀ D R_C=(P R_B₀ P) D R_C`, `R_C=(sI+C)⁻¹`, retains the original noncommutative factor order and does not assert commutation with `C`. This support claim depends on the actual compression and is not extended to arbitrary PSD `C`.

An independent imported audit at `/private/tmp/ra10-matched-leading-support-independent-audit.lean`, SHA-256 `4db731cb29d47a18201fbced1d8e3d6d386c68cc46c7ccdaee46486cbfc55a5d`, elaborated all five exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

The nuclear ideal property, Equation (14)'s nuclear norm inequality, compression Lemma 2, integral transfer, and frozen RA-10 Target remain open.
