# NM-03: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. The full canonical decision predicate is retained for every rational nonnegative m-by-n input and nonnegative rational threshold. Both factor matrices have actual real nonnegative entries and inner dimension two, with zero columns or rows allowed. The literal complete squared Frobenius sum and weak comparison retain exact equality, zero threshold, and rank-zero/rank-one products.

2. No exact-rank-two, symmetric, positive-definite, strictly positive, singular-spectrum or rational-factor promise is imposed on the target. The source hardness theorem happens to construct such restricted inputs, but its general decision language remains unrestricted as requested.

3. Natural dimensions cover all positive rectangular formats. The disclosed extension to empty formats merely supplies the standard trivial yes inputs for nonnegative threshold; it excludes no canonical instance and does not change the NP-hardness classification. This convention must remain visible in final notes.

4. The explicit encoder contains both framed dimensions, every rational entry in dense row-major order and the rational threshold. The existing encodeNat and encodeRat implementations were inspected: bit length framing is not unary-value encoding, signed numerators and positive reduced denominators are canonical, and zero is encoded as 0/1. No arbitrary input-size function or rational unit-cost model replaces binary length.

5. DecisionLanguage is the literal fixed binary language of valid encodings whose real factors satisfy the mathematical predicate. Malformed or sign-invalid words are negative under the stated ordinary-language convention. The target and optional P alternative use that same language; no abstract semantics parameter can reinterpret reduction outputs.

6. The inspected Complexity.ManyOneNPHard quantifies every language in concrete finite-verifier NP and then an actual finite transducer with a uniform polynomial runtime before every source word. PolynomialManyOneReduces requires an actual RunsWithin output and exact membership equivalence. It uses no oracle or independently supplied reduction map with an assumed cost.

7. FiniteMachine has finite three-symbol tape alphabet and finite control table, actual TM0 transitions, a genuine bounded trace ending at a halt and the exact terminal word. Complexity.InNP bounds certificate lengths and verifies actual binary pairs with a total finite verifier. These already reviewed definitions faithfully express the computational classification selected by the specification.

8. The retained manuscript Section 1 Theorem 1 states exactly polynomial-time many-one NP-hardness for this decision predicate and expressly does not assert NP membership. The proposed Target records that credited answer; optional PolynomialSolvability retains the P question without negating it or claiming mutually exclusive alternatives.

9. The complete manuscript was read. Its delta=1/(12N), epsilon=1/(24N^2), rational row projector, matrix I+(delta/N)*11^T-epsilon*P and threshold N-rank(C)-2+rank(C)*(1-epsilon)^2 match the supporting numerical record. These proof-construction constants are not new target restrictions or free computational primitives.

10. The later inverse-polynomial gap and simple-spectrum rational perturbation are correctly identified as strengthening results outside the required exact decision statement. No approximation-hardness ratio, strong NP-hardness, NP-completeness or finite diagnostic replaces the full target. General codec inversion/model translations and a reduction proof remain later proof work rather than blockers to defining the concrete proposition.

## Bound inputs

- docs/lean/statements/NM-03/NUMERICAL_TARGETS.md: 05545a0604dc7a411283d8eafb51b8182ad90c85b55e0dc1356202acce125dd2
- docs/lean/statements/NM-03/ORIGINAL.md: ede64b657c554d85902126936e807c0cb4a3863bdb0be57fc47a69e7adf93891
- docs/lean/statements/NM-03/source-lock.json: 77b13cc73aa4439cb2f51da6a5e49e95738d40b316a03ef2679039f25a3c9599
- lean-statements/NLA/Computation/BinaryEncoding.lean: d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a
- lean-statements/NLA/Computation/Complexity.lean: 0ad5ee64d5ef0b77f5531b31bb1b69a1a668c556cbd79b42fea7b6f108275c88
- lean-statements/NLA/Computation/FiniteMachine.lean: 7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d
- nonnegative-and-positive-factorizations/NM-03/README.md: ede64b657c554d85902126936e807c0cb4a3863bdb0be57fc47a69e7adf93891
- nonnegative-and-positive-factorizations/NM-03/problem.tex: 29bd68721c3bd588a219a5961e428a50ad2feee3a304fed0eaa65ce5f1eb4b12
- references/colbrook-factorization-2026-09-11/manuscripts/NM-03_rank_two_approximation_hardness.tex: 6499b57007a4961c94a2d5d729699cd2f5ab57cd6f89b5bcff7f57b84d265ba8

## Limits

Independent AI-agent preimplementation mathematical and computational specification review, independent of author /root. The full canonical page, complete retained manuscript, specification and named existing computational definitions were inspected; all source-lock bytes were verified. This approves exact statement correspondence, not a new proof audit of the reduction, a solver, or an as-yet-unwritten Lean target. Final source/import/pin and kernel/frozen-identity review remain required.
