# AA-01: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. The full canonical README, final approved specification, complete RoundedTree helper and controls, live/frozen Target and implementation notes were read. This reviewer authored neither specification nor implementation; author is /root/inventory. The exact finite arithmetic model and ordinary decision machine remain separate.

2. Program r is genuine finite inductive syntax with only register return, exact negation, rounded add/subtract/multiply and three-way comparison. Every operand and output is Fin r. No constant register, arbitrary real function, oracle, loop, division, exact sum/product or test-to-number instruction appears. The next arithmetic state has one appended register; previous indices are unchanged.

3. Program.evaluate is structural recursion over the actual finite tree. Fin.snoc preserves every old register and appends precisely the real arithmetic result times (1+delta), or exact negative. The pinned snoc definition and its castSucc/last identities were inspected. Stored result reuse preserves earlier error dependence; another rounded instruction, even with equal operands, uses a distinct coordinate.

4. roundedCount includes all rounded nodes across all branches. Each rounded node takes coordinate zero and supplies its successor tail. Comparison branches receive exactly disjoint blocks beginning at zero, less.count and less.count+equal.count. errorSlice constructs Fin indices with actual in-range proofs; no default zero error or inaccessible coordinate exists. Branch selection uses current rounded register values with exact less/equal/greater trichotomy.

5. Term and PolynomialInput contain actual integer coefficients, natural exponent vectors and a finite list. PolynomialValue sums every occurrence, including duplicate monomials and zero coefficients, using genuine natural powers and complete finite products. ValidInput is the collected p(0)=0 condition, preserving cancelled constant terms. Coefficients enter the symbolic encoding only, never the initial numerical registers.

6. encodePolynomial contains natural dimension and list length, then each signed coefficient and every exponent in increasing coordinate order. Its reused BinaryEncoding primitives use bit-length framing and canonical signed magnitudes. No coefficient, sign, exponent or count is omitted; the grammar has no output-dependent semantics. General inversion proofs remain future proof work, not an encoding oracle.

7. Accurate requires exact zero-error evaluation on every real input and then forall eta in (0,1), exists one u in (0,1), forall all real x and all independently bounded finite errors, the stated weak relative inequality. The same program is chosen before eta, and u is uniform over x/errors. Polynomial zeros force exact output zero. There is no absolute floor, probability law, generic-input guard or stable-branch assumption.

8. AccuratelyEvaluable quantifies actual finite Program syntax, not a supplied predicate or signed-gap criterion. At n=0 the no_program_zero proof inspects every constructor and its impossible Fin 0 index. The valid zero-variable polynomial is therefore a no-instance under the explicitly approved convention. For n=1, the control zero_tree_accurate proves exact subtraction zero for every error, including the full precision quantifier.

9. Target chooses a single ordinary FiniteMachine before every valid PolynomialInput, then a Boolean and a natural finite halting-time witness. The current shared finite alphabet/control table, actual TM0 trace, terminality and exact one-bit DecidesWithin semantics were inspected. No uniform polynomial time bound, real-equality oracle or gain/evaluator output is demanded. Behavior outside valid coefficient inputs remains unconstrained as specified.

10. All semantic controls were read. They check the square of a reused rounded sum, separate errors for recomputation, exact negation, equality and rounding-dependent comparison paths, branch-size counts, the greater/equal static error offsets, unused-branch independence, complete coefficient/exponent grammar, exact zero-polynomial accuracy and collected constant cancellation. Kernel trust is asserted for these meaningful symbolic checks; none proves the decidability target.

11. The final live/frozen modules import the same nominal Program/PolynomialInput and recursive evaluator definitions from RoundedTree. The frozen source matches the standard header and namespace substitution exactly. Target selects explicit LeanCert kernel trust and passes the shared closed-safe-Prop/allowed-axiom check. No target proof or target axiom is introduced.

12. The author-local final-inputs hashes match all current reviewed files. The retained author-executed receipt reports exit zero for the full ordinary/helper/control/live/frozen closure and the actual rfl identity theorem; Target and equality logs report only propext, Classical.choice and Quot.sound. This reviewer inspected those outputs without claiming a separately executed kernel run or Linux Comparator result. The report explicitly binds RoundedTreeControls and its complete local import closure as well as Target closure and all pins.

## Pinned external definition inspected

- Mathlib/Data/Fin/Tuple/Basic.lean: c9a91f26403ddab92eb0599176545bc834f6b1e242e420875c3401bbdd9db0b7; Fin.snoc preserves old indices and returns the new value at the last index.

## Author-local evidence inspected

- /private/tmp/nla-aa01-evidence/results.json: 6b5b2ba0ff6eed4f58656351e09b42e074839bd9474da23538390edd4c2abd6f
- /private/tmp/nla-aa01-evidence/final-inputs.json: f06fd7fd4ff7e920182f8a782a5a447997d7174b31e09a8f96e23120dbf97faf
- /private/tmp/nla-aa01-evidence/BoundaryIdentity.lean: 4055d272ea804b92020dc7f1d645bbe8175569b9be3e3c89cd951dde9f70261f
- /private/tmp/nla-aa01-evidence/NLA_Statements_Infrastructure.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- /private/tmp/nla-aa01-evidence/NLA_Computation_FiniteMachine.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- /private/tmp/nla-aa01-evidence/NLA_Computation_BinaryEncoding.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- /private/tmp/nla-aa01-evidence/NLA_Computation_RoundedTree.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- /private/tmp/nla-aa01-evidence/NLA_Computation_RoundedTreeControls.lean.log: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- /private/tmp/nla-aa01-evidence/NLA_Statements_AA01.lean.log: 212aa7c4ddad80a6596b98a6dd1d84812d1f67526ad789237da4af382669d7cf
- /private/tmp/nla-aa01-evidence/Reviewed_AA01.lean.log: 6aec9e4ada1dde9ae66b33a71d6f19b3058c1c08d508b2f655fdde1b687ecf45
- /private/tmp/nla-aa01-evidence/BoundaryIdentity.log: c9341ad5e1a6dbcd002c214e18b1bbe14d15594e644f07c2fbb36dca8025760b

## Bound inputs

- arithmetic-and-complexity/AA-01/README.md: 7c95575dd3b31fd6d9d0b6da31839c545a033e07eb58bba7e2eaf4e1d8a6f316
- docs/lean/statements/AA-01/IMPLEMENTATION_NOTES.md: 671fabd015872c47361430ed512b95d950e633880c0f98a357a45574199c049c
- docs/lean/statements/AA-01/NUMERICAL_TARGETS.md: ae12a6116c32ee45e2125512dc44d28783d6158e592853a98caa9d9806ff741d
- docs/lean/statements/AA-01/ORIGINAL.md: 7c95575dd3b31fd6d9d0b6da31839c545a033e07eb58bba7e2eaf4e1d8a6f316
- lean-statements/NLA/Computation/BinaryEncoding.lean: d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a
- lean-statements/NLA/Computation/FiniteMachine.lean: 7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d
- lean-statements/NLA/Computation/RoundedTree.lean: b12aa0ae03935b78f9d36abfe77862dedeb27503a66324617621c0c6ecf2c9d7
- lean-statements/NLA/Computation/RoundedTreeControls.lean: 4a0fc5e0c0e305f2ff287555a78f4e19db5d81e2e90e3a58b23b1804ffe38471
- lean-statements/NLA/Statements/AA01.lean: 8957840f7a5b678d019c85f154662ba1755c9a43f9398446bd2ea3a4a627f331
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/Reviewed/AA01.lean: 5cb25d70ebcf90ce6f1eba3704886013cdd3f10c3d859e3e97be731ae009efd2
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71

## Limits

Independent AI-agent source-level final fidelity review, independent of author /root/inventory. Approval covers exact mathematical/model definitions and bound bytes. Author-local build/identity evidence was inspected and separately recorded, not independently executed by this reviewer. No decidability proof, general syntax/encoding equivalence theorem, solver or Linux CI pass is asserted.
