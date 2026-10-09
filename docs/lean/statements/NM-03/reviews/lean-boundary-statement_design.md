# NM-03: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. The complete NMFDecision shared helper, live and frozen boundaries, final notes and actual FiniteMachine/BinaryEncoding/Complexity import closure were inspected. Input contains both arbitrary natural dimensions, the full rational rectangular matrix and rational threshold; ValidInput imposes exactly entrywise nonnegativity and nonnegative threshold.

2. Encode writes canonical framed row count, column count, every matrix rational in increasing row-major order and then threshold. Nested List.ofFn followed by flatten retains precisely rows*cols entries. The previously reviewed signed reduced rational and binary natural encoders retain every sign, numerator, denominator and dimension bit. No assumed encoding or cost function occurs.

3. MathematicalYes quantifies all real m-by-2 and 2-by-n factors with weak entrywise nonnegativity, and computes the complete squared Frobenius residual using an actual two-term inner product. The rational input and threshold cast exactly into reals. Equality, zero threshold and zero factor columns/rows remain; no rational witness, exact rank, symmetry or strictly positive restriction is added.

4. Empty formats have the explicit ordinary empty-sum convention from the approved specification and notes. They omit no positive rectangular format and do not introduce an unavailable default factor or output. DecisionLanguage is the exact fixed language of encoded valid yes inputs; other words are negative, with no separate analytic promise or oracle.

5. Complexity.ManyOneNPHard expands to every concrete InNP language, one finite transducer and one uniform polynomial bound before every word, an actual bounded output run, and exact membership equivalence to this same DecisionLanguage. The underlying finite alphabet/table, TM0 transitions, terminality, output suffix, certificate and pair encodings were inspected. No favorable reduction oracle, free evaluator, assigned cost or numerical equivalence substitutes for NP-hardness.

6. PolynomialSolvability separately retains the original P alternative through the concrete InP definition, which uses a total actual finite decision machine on binary words. Target does not negate it, claim P!=NP, assert NP membership or NP-completeness, or claim the original alternatives exhaust every possible classification.

7. The nominal Input type and all data-language helpers now occur once in NMFDecision, imported identically by both statement namespaces. These are the same mathematical bodies reviewed in the specification. This corrects actual definitional identity without changing the target, and binds the full helper rather than hiding a type mismatch behind a textual comparison.

8. Both PolynomialSolvability and Target are safe closed Prop definitions with explicit kernel trust, separate #assert_statement and #assert_trust kernel checks, and standard-three axiom reports. The full local closure, shared helper, pins and final notes are bound below. No declaration proves either proposition.

9. The current root author-local receipt binds shared/live/frozen source hashes and reports exit zero. The retained CheckNM03 source contains actual rfl equalities for BOTH propositions, and its log reports only propext, Classical.choice and Quot.sound for each; live/frozen logs do likewise. This reviewer inspected those actual results without claiming an independently executed kernel or Linux Comparator run.

10. The earlier nominal-type identity failure and corrective pre-final-review shared-helper move are accurately disclosed in the notes. Frozen bytes exactly match the live body under only the standard comment and namespace rename. The rejected identity was not accepted and no statement, trust or equality safeguard was weakened.

## Bound inputs

- docs/lean/statements/NM-03/IMPLEMENTATION_NOTES.md: 85b38432f4e4ce19eb4d021aa8845f93458b13f92c5e81c48e8fe16c379ff03c
- docs/lean/statements/NM-03/NUMERICAL_TARGETS.md: 05545a0604dc7a411283d8eafb51b8182ad90c85b55e0dc1356202acce125dd2
- docs/lean/statements/NM-03/ORIGINAL.md: ede64b657c554d85902126936e807c0cb4a3863bdb0be57fc47a69e7adf93891
- docs/lean/statements/verification/2026-09-28-nmf-hardness/CheckNM03.lean: 336bb75b516ffac39f5953a330252b823fe955a8bb4e95720c076ae52e5b4b05
- docs/lean/statements/verification/2026-09-28-nmf-hardness/CheckNM03.log: c3d5ef2852baa610ef76abcef4f85d929c991f50c6c87199d26fd2ae648fdefb
- docs/lean/statements/verification/2026-09-28-nmf-hardness/NLA-Statements-NM03.lean.log: baacdf9706ddae186d05549cc40f9b47e6358b35dfac2dc72a4e2c5d2b8ca206
- docs/lean/statements/verification/2026-09-28-nmf-hardness/NLA-Statements-NMFDecision.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- docs/lean/statements/verification/2026-09-28-nmf-hardness/Reviewed-NM03.lean.log: 22f29b501267967ffb41e13f00282a0227dc622b5f22a54129ffb0f6a1c773ca
- docs/lean/statements/verification/2026-09-28-nmf-hardness/receipt.json: adab482263f9452b231d7bb66e11cdc2012acc2f76f6f5e1155adbea6d6a6924
- lean-statements/NLA/Computation/BinaryEncoding.lean: d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a
- lean-statements/NLA/Computation/Complexity.lean: 0ad5ee64d5ef0b77f5531b31bb1b69a1a668c556cbd79b42fea7b6f108275c88
- lean-statements/NLA/Computation/FiniteMachine.lean: 7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/NM03.lean: a102852431e814ede601a0b7807624824fb5dce48e541e0b0b788334ce406a26
- lean-statements/NLA/Statements/NMFDecision.lean: b3275a10b006f9f2ed635dc7249ff5c71d4e6acc3c3e943cfddf4b0183fb51af
- lean-statements/Reviewed/NM03.lean: d51409f14f7db1628820b1892a8b2700b500a8b1c5e13e42bc212d768cefa267
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- nonnegative-and-positive-factorizations/NM-03/README.md: ede64b657c554d85902126936e807c0cb4a3863bdb0be57fc47a69e7adf93891

## Limits

Independent AI-agent final source-level fidelity review, independent of specification/implementation author /root. Approval concerns the exact mathematical and finite-machine meanings of these bound sources. It is not a proof of hardness or polynomial solvability, a new reduction audit, or an independently executed kernel/CI run. The root-executed compilation evidence is explicitly author-local.
