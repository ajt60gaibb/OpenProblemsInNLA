# Independent review 2: finite shared-label garden trees

Reviewer: `/root/solved_inventory`, AI agent, 17 October 2026.
Verdict: **APPROVE GardenTree and LSSGarden at the hashes below, as partial exact expansion infrastructure. No full-target noncancellation or SP-11 proof is certified.** I did not author or edit these modules.

I read the full sources and independently recompiled both with the pinned Lean runner. The unchanged-source checks, actual logs and successful exit codes are retained in [new-gates-review-2-evidence/result.json](new-gates-review-2-evidence/result.json). LeanCert kernel assertions passed and the audited exports report only `propext`, `Classical.choice`, `Quot.sound`. These are local development checks, not isolated Linux Comparator receipts.

`GardenTree` is a finite inductive rose tree with child arity fixed by the original label. A full coloring chooses the output conduit color at every actual node occurrence. The weight multiplies the coefficient at that node by every child's recursive weight. The coefficient accesses the one form indexed by that node's label; separate occurrences never gain independent coefficient variables. Its finite-sum theorem is a direct multilinearity expansion with one basis vector at the root output. It includes arbitrary arities and empty ambient coordinate types without asserting nonvanishing.

`LSSGarden` uses the same strict vertex-index measure as the actual uniformLSS recursion. Its children are precisely priorVertex entries, with strict decrease proved by the existing predecessor lemma. The evaluation identity is proved by well-founded induction and the literal recursion equations on both sides. Consequently its polynomial row expansion is for the actual shared-variable polynomialLSS matrix, rather than a separately assumed tree model. No cancellation argument is hidden in the construction or imported as an axiom.

These results do not show a single diagonal or edge polynomial is nonzero. A double-root expansion must still identify the two root colors, retain every node occurrence, extract the exact shared-variable exponent/sign, and prove uniqueness of a nonzero coefficient for greedy orders. The final unconditional Target, independent final scope reviews and Linux Comparator checks remain absent.

| Reviewed source | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP11/GardenTree.lean` | `4331044b43df97a3c3640350441434edc806ca7ba90c0b724ec70ad86035cbf9` |
| `lean-statements/NLA/Proofs/SP11/LSSGarden.lean` | `750d24afc21f583b09d2eff5308aca8df6a71d913d9f6ad5d0ae1b0b006949b4` |
