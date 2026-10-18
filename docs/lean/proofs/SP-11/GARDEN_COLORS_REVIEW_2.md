# Independent review 2: all-tuple signed coefficient classification

Reviewer: `/root/solved_inventory`, independent AI agent, 17 October 2026.
Verdict: **APPROVE GardenColors at the hash below as an exact coefficient classification. No recursive graph noncancellation or full Target proof is certified.** I did not author or edit this module.

The full source was inspected and independently recompiled successfully with the pinned Lean runner. The unchanged-source hash, command, output and kernel axiom report are retained in [new-gates-review-2-evidence/result.json](new-gates-review-2-evidence/result.json) and `GardenColors.log`. LeanCert kernel checks pass; exported closures contain only `propext`, `Classical.choice`, `Quot.sound`. This is a local development run, not isolated Linux Comparator acceptance.

For an injective finite color tuple, the code takes the actual finite image and proves its cardinality. Its increasing order isomorphism supplies a coordinate subset, and the inverse image positions give a bijective finite permutation. The tuple equals that increasing subset composed with the permutation at every index. The chosen subset and permutation depend on the color tuple and proposition proofs, not on a new occurrence label. The first-output alternating convention therefore yields the actual signed shared variable.

`colorExponent` assigns precisely one copy of that variable when colors are distinct; it assigns zero exponent to a repeated-color term. `colorSign` is the actual alternating sign acting on one, and zero when a color repeats. The all-tuple theorem proves that the original universal polynomial coefficient equals the literal monomial at this exponent and scalar. The repeated-color case is genuinely zero by alternation, so its exponent convention cannot add a spurious contribution. The nonzero-sign lemma requires a nontrivial ring and uses the fact that a permutation sign is one or minus one.

This classification is sufficient to extract each actual occurrence's monomial without any favorable-presentation hypothesis. It does not show that the sum of different occurrence-colorings has a nonzero coefficient. In particular, the finite occurrence expansion and the graph-specific uniqueness of a contributing exponent remain separate obligations. No canonical page, frozen target, permanent ID, or earlier checkpoint source was changed.

Reviewed source: `lean-statements/NLA/Proofs/SP11/GardenColors.lean`.
SHA-256: `2ebf942b4a67b15d8a4a055ff0a435039ca0f07ce5a5e85711d8dcf7e64dd198`.
