# PF-05 independent pre-proof challenge review

**Reviewer:** Codex agent `/root/pf05_second_statement_referee`, independently reviewing the packet prepared by another agent and the separate `/root` review.  
**Date and checkout:** 16 October 2026, commit `b726615b89280b02d698a047da0070209d9c2c7c`.  
**Verdict:** **APPROVE the exact pre-proof statement and Challenge boundary.** I found no hidden weakening of the canonical PF-05 question or its numerical scope. This is not approval of a Lean proof.

## Source identity and pins

The published base is `47006df8b3a6c724a557266c891893d03e69323a` (`origin/main` in this checkout). Its PF-05 README is byte-identical to the current canonical README and `docs/lean/statements/PF-05/ORIGINAL.md`. I independently recomputed the hashes in `SOURCE_LOCK.json`: all 13 source/project hashes matched and all five local copies matched their shared statement-package sources. The reviewed pin file itself has SHA-256 `534b29e94ec4e00c67d47e78818f054a120c8087d10a2f58897a19e7fd675d88`.

| Reviewed material | SHA-256 |
| --- | --- |
| Canonical `PF-05/README.md` and preserved `ORIGINAL.md` | `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71` |
| `NUMERICAL_TARGETS.md` | `d5c00daa8a0bfa9b520c999b017217ab07fe9bb76b2cac6240f12f241b5db184` |
| Authored mathematical manuscript `PF-05_rigidity_with_zeros.tex` | `fab2b46fb396aea58744c5b90bb5795b95e7c84819a62d73d31e54dbd5d784d6` |
| Local `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| Local `NLA/Statements/PF05.lean` | `3ac9a2fb395d96c3b61c6f2593144caac010da4bfafd2d96f86627aa7a75859d` |
| Local `Reviewed/PF05.lean` | `df79daee68563e5bb6a6d85cf70246bf2154f12bcc5fe5a6a806e8009e558b7f` |
| `Challenge.lean` | `6ad5b632ae12132c8a932eb40b24c028c9fe608bf7bd0eca40e91daa46ba207f` |
| `Check.lean` | `da82602cf2fc9822931f9bbfea90340f6d173b3d4aa9120b6ee980217ea614f9` |
| `comparator.json` | `d6ef9cf41e9b997a0404f6e591a3ba9f85576d381b370c5bf42bc7380284a36d` |
| `lakefile.toml`; `lake-manifest.json`; `lean-toolchain` | `dcd8c235a9f7c26db77eff9a30234144116132d6a25d41eed9cccdd52989d420`; `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`; `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The package pins Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`; the manifest fixes the transitive package revisions. The local statement, reviewed statement, infrastructure, manifest, and toolchain are byte-for-byte copies of the paths listed in `SOURCE_LOCK.json`.

## Mathematical and Lean boundary comparison

The canonical question asks for the equivalence for **every fixed** real size-two PSD factorization of an entrywise nonnegative `p × q` matrix with ordinary rank exactly three and real PSD rank exactly two. `NLA.Statements.PF05.Target` quantifies over all natural `p,q`, all such matrices, and all such fixed factor families. `M.rank = 3` rules out empty dimensions. `PSDRankTwo` means existence at size two and nonexistence at size one, exactly the positive-integer minimum in the README. The quadratic-form definition of PSD includes symmetry and permits zero, repeated, rank-one, and rank-two factors. Neither target nor factorization imposes positive entries, nonzero rows/columns, positive definiteness, distinctness, normalization, or a prescribed zero pattern.

`FeasibleDirection` quantifies over real symmetric `E_i,F_j`, imposes `trace(E_i B_j) + trace(A_i F_j) = 0` for every pair, and requires one strictly positive `h` on which every **straight** segment `A_i+tE_i`, `B_j+tF_j` is PSD for all real `0 ≤ t < h`. It does not demand that perturbed factors reproduce `M` at positive time. The single `d` in `InfinitesimallyRigid` applies to all row and column factors with opposite signs, as in the canonical first condition.

`UniqueUpToCongruence` quantifies over every other complete size-two PSD factorization of the same `M`. It requires one real `2 × 2` matrix `S` with `S.det ≠ 0`, shared across all factors, with primal action `Sᵀ A_i S` and dual action `S⁻¹ B_j (S⁻¹)ᵀ`. This is the README's congruence convention and preserves the trace pairing. The inverse is guarded by the nonzero determinant. `Matrix.rank`, `Matrix.trace`, matrix multiplication, scalar action, and the explicit quadratic form carry their ordinary real meanings; there is no opaque numerical predicate or certificate.

The authored manuscript's Theorem 1 has the same universal domain and equivalence. Its proof explicitly discusses zero rows and columns, a nonzero orthogonal pair, singular and repeated factors, and the positive-entry case. This review uses the manuscript to confirm *scope*, not to certify its proof. `NUMERICAL_TARGETS.md` likewise specifies exact real equalities and no numerical computation or tolerance; the Lean target adds none.

`Challenge.lean` states exactly `NLA.PF05.target : NLA.Statements.PF05.Target`; its sole `sorry` is the intentional challenge hole. `Check.lean` asserts both target declarations and their kernel trust boundary, then states definitional equality of the live and frozen targets by `rfl`. The frozen file has the same definitions under `NLA.ReviewedStatements.PF05`. Comparator selects only `NLA.PF05.target`, with `solution_module` `Solution`, no definition targets, and permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. It does not select a weaker lemma.

## Limits and conditions for later claims

This is source and hash review. I did not run `lake build Challenge Check`: this worktree has no `.lake` packages and the pinned Lean 4.33.1 toolchain is absent locally. I did not run Comparator or inspect any `Solution.lean` (none exists), and I did not audit or formalize the manuscript's proof, including its cited positive-entry theorem. The `#assert_*` commands and `rfl` check express an intended statement identity; their successful elaboration in this isolated package remains to be established by a later build. A future proof must discharge the full target with the pinned dependencies and allowed axioms. Any substantive statement, challenge, configuration, or pinned-source change reopens this review.
