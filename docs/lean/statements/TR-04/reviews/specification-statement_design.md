# TR-04: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. The statement retains every d>=3, every mode n_i>=2, every positive prescribed r_j, and every real dense tensor. Actual unfolding matrices across all d-1 cuts and real matrix rank fix the canonical TT feasibility set, including overprescribed ranks, deficient inputs and zero tensors.

2. The infimum is the actual attained optimum: zero is feasible, the intersection of determinantal rank constraints is closed, and bounded minimizing sequences have convergent subsequences in the finite real tensor space. The target therefore keeps strict error<(d-1)E* when positive and exact tensor equality at zero, with no rank increase or uniform smaller factor.

3. A single finite program and polynomial constants precede every format, rank vector and tensor. This implements the affirmative branch of the canonical algorithm-or-obstruction request without pretending to prove the algorithm exists. Dense size plus dimensions plus numerical rank sum is a polynomially equivalent scale for the stated arithmetic model, not a bit-length complexity claim.

4. The proposed ordinary scalar RAM has explicit fixed finite syntax, finite registers/constants, actual reads/writes and arithmetic, no real-to-natural digit extraction, and distinct arithmetic failure. This removes the old arbitrary Tensor->Tensor x Nat evaluator and its unrelated candidate-count runtime field.

5. The rectangular SVD instruction has complete full U,V orthogonality, ordered nonnegative sigma, and exact rectangular reconstruction. Old-store input reads, disjoint output blocks, unchanged other storage and polynomial cubic charge account for actual bulk output. All additional products, reshapes and error calculations must be executed through charged scalar instructions.

6. All valid SVD replies, including ties and zero-space bases, are universally quantified along actual legal trajectories. This is an explicit robust exact-SVD primitive convention, not an unproved equivalence to an arbitrary answer-encoding deterministic selector. It matches the intended unrestricted SVD primitive and the archived solution: its first tied basis is expressly arbitrary, its cyclic projector averaging identity works for every such basis, and subsequent TT-SVD bounds permit arbitrary valid truncations.

7. The exact input layout contains only format, prescribed ranks and every tensor entry under the last-index-fastest mixed-radix bijection. No optimizer, unfolding-rank table or E* oracle enters execution. Output uses exactly N entries of the same tensor shape. Charged cast/comparison loops can recover supplied integer shapes within a polynomial in numerical input ranks.

8. Existence of a legal trajectory is paired with correctness and polynomial accumulated cost for every legal trajectory. Absorbing terminals have zero cost; all executed running instructions have positive cost. Failed or nonterminating choices do not count as successful outputs, so the target neither permits favorable nondeterministic branches nor vacuous semantics.

9. The complete archived manuscript was read. Its completion estimate, finite cyclic-window list, equality case e^2=E*, zero optimum and fixed-format ratio approaching two all agree with the retained specification. At most n1 candidates alone is correctly distinguished from full arithmetic cost. The source arbitrary tie proof supports the robust reply model without adding a new mathematical approximation restriction.

10. The old Challenge and Solution were read. Their arbitrary unfoldingRank field, format-specific evaluator and supplied natural count indeed fail to state a uniform polynomial-time algorithm. The new specification requires concrete machine definitions before any complete Lean-boundary approval; it does not require constructing a solver or proving its guarantee merely to state that proposition.

## Bound inputs

- docs/lean/statements/TR-04/NUMERICAL_TARGETS.md: f1bfd6d4a73a326a5dec79c052dba4f5ae38cc2f4c9e40622492a7694c5074f4
- docs/lean/statements/TR-04/ORIGINAL.md: 614dfc1189a99b0c2de54a04b948c01d35301d468e0b723c7fcb34b9918957cf
- docs/lean/statements/TR-04/source-lock.json: 1203a4fc275f4c0624db2673ec1535e4b5a71a810c5a10c599548066f6660b72
- references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-04.tex: e7770aa08ee91fbda82e0bfe3e087f1a9c8ee2a076218144bf0040e4d282bf73
- tensor-computations/TR-04/README.md: 614dfc1189a99b0c2de54a04b948c01d35301d468e0b723c7fcb34b9918957cf
- tensor-computations/TR-04/lean/Challenge.lean: e2593ab837691309d993bc46c77c5d37e8c12e9c975254324adbebace2246f32
- tensor-computations/TR-04/lean/SPEC.md: 9a67b4545286ff189a6c12c880862df4ca1767e1da3107c4509569d8a3600902
- tensor-computations/TR-04/lean/Solution.lean: dd02b5ba519b14e19aeebd005a72c85aba30084347bc3e82d5d8f61d4a94aa75
- tensor-computations/TR-04/problem.tex: 5b07e197470623eb5b26cca49d4a78a6bfba580c36442c8ee456abacb536ef36

## Limits

Independent AI-agent preimplementation specification review. Reviewer /root/statement_design did not author this specification. The full canonical page and cited archived source were inspected and source locks checked; this report approves mathematical/model correspondence only. No new Lean implementation, target proof, executable solver, or numerical certificate is approved. Final source/import/pin and actual kernel/frozen-identity reviews remain required.
