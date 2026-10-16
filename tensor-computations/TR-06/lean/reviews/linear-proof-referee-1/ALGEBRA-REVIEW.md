# Independent proof review: finite-generator character bound

Reviewer: `/root/tr06_statement_referee_1`, AI agent, nonauthor of AlgebraFiber.lean. Phase: post-proof auxiliary contribution review. Date: 2026-09-24. I previously approved its exact mathematical boundary before implementation.

**Verdict: APPROVE for integration.** No substantive changes requested. This is contribution-only approval, not geometric fiber identification or complete TR-06 verification.

Source SHA256 `a8cc251e23993c897b8a7d936334b55afac4a66d22393b9148af7a0c4fae9122`; approved plan SHA256 `63a825db06cab6e0e33287033605861bf1dc1d6311224b553804bd4310c93d7d`. The full source and plan are frozen under source/. The reviewer snapshot still matches the author source. I read every declaration and the relevant pinned Mathlib facts.

The theorem card_algHom_finset_le_of_span_eq_top has exactly the approved assumptions: R and A are commutative rings, K is a field, and A and K have arbitrary R-algebra structures. A family g:Fin N→A spans A over R. The conclusion bounds every finite subset of R-algebra homomorphisms by N. There is no hidden finite-free-module, faithful algebra action, domain assumption on R or A, or separability requirement. Importing a file whose name includes FreeModule does not impose an instance on this theorem.

The proof defines evaluation as a K-linear map from R-linear maps A→K to K^N. Its injectivity follows by LinearMap.ext_on_range from the supplied spanning equality. I checked that this library theorem only extends equality from the span; it does not demand a basis. Mathlib's linearIndependent_algHom_toLinearMap, read in LinearAlgebra/LinearIndependent/Lemmas.lean, asserts independence over the target integral domain and does not require an injective R→K. The proof restricts that independent family to q, transports it through injective evaluation, and applies the finite-dimensional bound in K^N. Thus the cardinality bound is uniform over the chosen R-algebra action on K. With N=0 the same finite-dimensional argument bounds the finite subset by zero; there is no positive-N premise or illicit selection of a generator.

The theorem bounds finite subsets as specified. It does not by itself identify algebra homomorphisms with tensor points, construct a finite envelope, prove Noetherian compactness, or establish a generic/quasi-finite locus. Those omissions are correctly documented and do not weaken its approved supporting statement.

The author/affiliation header gives George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, without email, and retains Matthew J. Colbrook's original TR-06 proof attribution. The implementation uses the existing Artin-independence API rather than re-proving it. No source attribution issue or misleading whole-problem claim was found.

Independent verification: recheck.py rebuilt this snapshot with pinned Lean 4.33.1 and LeanCert in the isolated review build, using only pinned package caches. AlgebraFiber-receipt.json records the full command, environment, source/log hashes and exit zero. logs/AlgebraFiber.log contains no warnings/errors. generatorEvaluation_injective uses exactly [propext, Quot.sound]; the cardinality theorem uses exactly [propext, Classical.choice, Quot.sound]. Both #assert_trust kernel checks pass. No sorry, admit, custom axiom, native_decide, unsafe or Challenge import appears. The reviewer-owned source/ReviewBoundary.lean independently elaborates exactly the approved universal character statement with no extra typeclass assumptions and passes its own kernel assertion.

Limits: no fresh dependency rebuild, Linux replay or Lean4 Comparator is claimed. Final whole-TR06 review and verification gates remain separate.
