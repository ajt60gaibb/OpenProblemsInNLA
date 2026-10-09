# IV-04 independent preimplementation specification review

Reviewer: `/root/infra_audit`, OpenAI Codex AI agent independent of specification author `/root/inventory`. Phase: `specification`. Verdict: **approve**.

The dimension restriction is exactly n>=1 and the united set consists of all real x for some independently admissible real T,b with Tx=b. Thus inconsistent and consistent singular instances, disconnected projections and unbounded sets remain included; inversion is not used.

The one global empty tag is equivalent to an empty united solution set. The box alternative explicitly requires nonemptiness. Finite lower/upper endpoints combine the universal one-sided bound with arbitrarily close epsilon witnesses, exactly characterizing infimum/supremum without demanding attainment or a common endpoint witness. Infinite tags mean strict unboundedness in the corresponding direction for every real threshold. Separate lower/upper types rule out the impossible infinity directions.

The output syntax explicitly encodes the global tag, original dimension, and each lower/upper endpoint pair, with context-specific infinity tags and exact canonical finite rationals. No extra output bits or omitted coordinates are permitted. RHS intervals are appended in fixed order after the band data with no duplicate dimension.

I checked the historical HullCase definition and its defect: n=1, T in [-1,1], b=1 yields two disjoint rays, whose hull is the entire line. The specification correctly asks for hull endpoints rather than making the projection itself an interval. Its listed empty, all-real, one-sided and bounded regression cases agree with the exact united-set semantics.

The credited joint manuscript Section5 gives finite rational endpoints through rational orthant polyhedra, including empty/unbounded cases. Its regular point-RHS hardness family and rational-reconstruction bound are retained proof context and do not narrow the universal input domain.

The entire canonical README and preserved original were read and compared byte-for-byte. The existing solution status and credited manuscript classify complexity without asserting P unequal to NP or an unconditional polynomial algorithm. Target keeps the original algorithm-existence question; a later equivalence to PEqualsNP is a separate proposition.

The specification selects a single actual finite binary transducer and one positive-coefficient natural-exponent polynomial before every dimension and rational input. RunsWithin refers to actual initialization, charged move/write execution, terminality and exact complete output. This preserves uniform polynomial time in all input bits and excludes a free evaluator, real-arithmetic cost, arbitrary complexity fields or a separate machine per instance.

The compact band encoding contains n, every diagonal interval, every upper interval and every lower interval in fixed order, with canonical framed rationals and no uncounted off-band data. Ordered endpoints include zero widths and zero crossings. All real in-band entries vary independently, even when interval data coincide; all off-band entries are zero. No promise of nonsingularity or sign is inserted.

No numerical approximation or sample enumeration is needed for these propositions. The historical proof files remain preserved. Kernel elaboration and frozen identity will check the eventual statement boundary but do not establish its truth; final mathematical/source review is still required after implementation.

This is a mathematical and computational boundary review of the exact specification bytes, not external human review or a proof of a polynomial algorithm or complexity classification.

## Bound inputs

- `docs/lean/statements/IV-04/NUMERICAL_TARGETS.md`: `53aee2b51e51b95459640c52d6c3f09186bca4bf180b7ede0b0380145f1962c2`
- `docs/lean/statements/IV-04/ORIGINAL.md`: `bea3f7d4322d1293944253138d3ee6f6f1fce1b1451084bfe3b6c716035c0735`
- `docs/lean/statements/IV-04/source-lock.json`: `57df03550b721a9097192f3b49e21be98aa76fe33c1f1f253d4404652a30cb8f`
- `intervals-and-absolute-value-equations/IV-04/README.md`: `bea3f7d4322d1293944253138d3ee6f6f1fce1b1451084bfe3b6c716035c0735`
- `intervals-and-absolute-value-equations/IV-04/lean/Challenge.lean`: `36553e3936946dfed7e404a08cfc595d8d91904e7b9d0798c12ace646a1b571f`
- `intervals-and-absolute-value-equations/IV-04/lean/Reduction.lean`: `af22f828b705007d482925aad5b9ef685e053107d76edd4757126d0b6b63b06c`
- `intervals-and-absolute-value-equations/IV-04/lean/SPEC.md`: `9021fced77a449f3ce78bca4bbd12764511b5d6b7dc92fb9e036febc987f7b9a`
- `intervals-and-absolute-value-equations/IV-04/lean/Solution.lean`: `6cbc2244861bde6c9a71b98c771547c549ee662c474441f6e592ff7119d7c581`
- `intervals-and-absolute-value-equations/IV-04/problem.tex`: `25028de6726fe52abe62d21f1d523b5f5578ebb9435709f42c4964bc062dd62b`
- `lean-statements/NLA/Computation/BinaryEncoding.lean`: `d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a`
- `lean-statements/NLA/Computation/FiniteMachine.lean`: `7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `references/colbrook-intervals-2026-09-11/manuscripts/IV-02_IV-04.tex`: `fffed1605054c4a3fa42fcb367286dba6ff5b829555a3e717827c448095cbb0c`
