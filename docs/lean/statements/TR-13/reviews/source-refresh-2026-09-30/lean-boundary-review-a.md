# TR-13 Lean-boundary source-refresh review A

Phase: `lean-boundary`.

Reviewer: `/root/refresh_tr13_review_a`, an OpenAI Codex AI agent independent of statement author `/root`. Date: 2026-09-30. Verdict: **approve** for the exact statement-fidelity scope and input bytes bound below.

This is a fresh source re-review after the existing implementation. I did not author the specification, Lean statements, frozen boundary, or source-provenance changes. I have not rerun Lean, a kernel checker, or Linux Comparator. This report does not certify the truth of `Target`, the separate complete-proof project, or the verification claims in the newly added notice.

I compared the complete current canonical README and byte-identical `ORIGINAL.md` against `previous-original.md`. The only canonical change is the 30-line complete-Lean-formalization notice; the retained mathematical Statement, status and credits are unchanged. The notice itself distinguishes its local build claims from pending authoritative Linux and independent final-review gates. I compared the archived and current specifications: only the provenance paragraph preceding `## Exact target` changed; all mathematical specification text from that heading onward is byte-identical.

The original preimplementation specification and source are preserved separately, together with `previous-statement.json` and the unchanged historical reports in the parent directory. I read those historical reports and their recorded chronology. This present review does not pretend to have occurred before implementation or replace that historical evidence with a backdated approval. The refreshed provenance paragraph accurately distinguishes the historical source hash from the current snapshot.

## Independent inspection of the complete local boundary

I read both `NLA/Statements/TR13.lean` and `Reviewed/TR13.lean`, and their full repository-local import closure: `NLA/Statements/TR14.lean` and `NLA/Statements/Infrastructure.lean`. I also read all three package-pin files. Their hashes match those bound in both preserved historical boundary records. The frozen TR13 file is exactly the live file with the prescribed leading comment and namespace substitution. No local imported definition or pin changed during this refresh.

The imported `TR14.HankelIndex` uses the full zero-based sum, proves its bound by `m*(n-1)+1`, and `Hankel` indexes the given coefficient vector at that sum. `OrdinaryWidth` is an actual finite sum of arbitrary products with independently chosen mode vectors. `SymmetricWidth` is a finite sum of complex scalar-weighted pure powers. For this positive-order target their padding semantics are rank at most the given width, including width zero; no rank oracle or hypothesis asserting equality is imported.

`VandermondeVector` has exactly the prescribed homogeneous entries. For `i : Fin n`, `i.val <= n-1`, so natural subtraction in its first exponent has the intended value. `VandermondeWidth` requires each parameter pair not to be jointly zero while allowing either coordinate to vanish, with no distinctness, affine-only, nonzero-weight, positivity or real restriction. Its coefficients may vanish, retaining padding.

`OrdinaryBorderWidth` quantifies `T : Nat -> ((Fin m -> Fin n) -> Complex)` and imposes only ordinary width at each sequence index. `SymmetricBorderWidth` uses the same ambient sequence type but imposes symmetric width. Both demand `Tendsto` to every coordinate using `atTop` and complex `nhds`. This retains unrestricted ordinary ambient limits and non-Hankel symmetric limits.

`EqualFiveRanks` universally quantifies every natural threshold and explicitly conjoins ordinary-width equivalence to each of the other four widths. Padding and finite decompositions, as explained in the accompanying specification review, justify the correspondence to equality of the five minima. `Target` retains `5 <= m`, `Odd m`, and `2 <= n`, then existentially chooses an actual `MvPolynomial` on all Hankel coefficients, explicitly witnesses nonemptiness, and requires `EqualFiveRanks` at every nonzero evaluation point. This is the complete original generic equality target, without adding the background numerical formula or the all-Hankel TR-14 question.

`Infrastructure.lean` checks that a statement is a safe definition with closed type `Prop`, and rejects axiom closure entries other than `propext`, `Classical.choice`, and `Quot.sound`. The live and frozen modules contain the global kernel-trust setting, `#assert_statement Target`, and `#assert_trust kernel Target`. I inspected these command definitions/usages as source; I did not execute them in this review. The sources contain concrete proposition definitions, not a proof or assumption of `Target`.

The package pins Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and immutable revisions for the transitive packages. This refresh rechecks the local closure and unchanged pins; it does not claim a fresh audit of all external dependency source files. The imported complex, finite-sum, polynomial-evaluation and convergence APIs preserve their ordinary mathematical meanings in the unchanged boundary.

No source-level boundary-fidelity blocker remains. Approval covers the current source bindings and unchanged mathematical boundary. Fresh elaboration, trust/control execution and Linux Comparator verification remain separate checks; an identity certificate equating two propositions would not prove either proposition.

## Reviewed input hashes

- `docs/lean/statements/TR-13/IMPLEMENTATION_NOTES.md`: `11300fbbcd0c6c4917d4a49a30de552ad71d155778673576cb63d345208a7d15`
- `docs/lean/statements/TR-13/NUMERICAL_TARGETS.md`: `8238e5adadcc23223017e7900a751f9cd0318b5375886b5543b4b8eb9303d91d`
- `docs/lean/statements/TR-13/ORIGINAL.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
- `docs/lean/statements/TR-13/reviews/lean-boundary-inventory.md`: `2bd75b81be09a6fee20b8fa910538abe80691c0f1f94ae3123cbf14b472066ff`
- `docs/lean/statements/TR-13/reviews/lean-boundary-statement_design.md`: `f311c05b9e3c63be19bb290ad30892dedb6ebd60785c5b75aee566db0d1b2f9b`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/README.md`: `abd6d3efd86f6431f3e19590480dc141b0eefec9a5c51952aab4e97aedce8fdd`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-original.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-specification.md`: `1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-statement.json`: `2db388f56748ad553da877334d097ecc01898f11e1523b3da857c03d5d0bdc7c`
- `docs/lean/statements/TR-13/reviews/specification-infra_audit.md`: `bcf09c23139f384ebcb7274f0d745845479b7a433dc62793307b57028fcbeb3d`
- `docs/lean/statements/TR-13/reviews/specification-statement_design.md`: `539fe8aa02e30b71103d5fcf4a929d001d621e0ca50c81b87e6b85412e9a2a79`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/TR13.lean`: `5b43b0a5410d91a7ec9a796a3e6d7cdd50f75929797d2eca4587cb2b0905a99d`
- `lean-statements/NLA/Statements/TR14.lean`: `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9`
- `lean-statements/Reviewed/TR13.lean`: `8b876a24f87eeecdb983ca6044b7548aa629db0a3f0fe9c3878516cba8b29b16`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `tensor-computations/TR-13/README.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
