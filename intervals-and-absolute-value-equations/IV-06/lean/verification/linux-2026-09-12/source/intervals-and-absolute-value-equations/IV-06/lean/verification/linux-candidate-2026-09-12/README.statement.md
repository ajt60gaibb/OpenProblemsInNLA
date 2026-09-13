# IV-06 Lean formalization: statement review candidate

This package states the complete negative resolution of the original independent-entry interval-eigenvalue component bound. The definitions and eight Challenge declarations have been freshly type-checked, with eight deliberate placeholders. **No proof or Solution implementation exists at this stage.** Two independent statement approvals must bind these bytes before proof work begins. The canonical problem remains **Solved** on the strength of its existing informal resolution; no Lean-verified status is claimed.

The mathematical counterexample is Matthew J. Colbrook's, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization is prepared for **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance. This records distinct mathematical and formalization roles and makes no priority or human peer-review claim.

## Exact target and scope

The original family includes every real matrix between its lower and upper endpoints entrywise; all entries vary independently and singleton intervals are allowed. A real eigenvalue requires an actual nonzero real eigenvector. The component count is the cardinality of Mathlib's `ConnectedComponents` of the attained real-eigenvalue subset with its real subspace topology. Infinite component sets do not acquire a spurious count of zero. No symmetry, diagonalizability, compactness or finiteness assumption is added.

The full original universal statement ranges over every positive dimension and every valid real interval box. The proposed proof establishes an admissible dimension-three box with at least four actual components, then negates that universal statement. It does not claim exactly four components or calculate all component endpoints.

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) first, then [Definitions](NLA/IV06/Definitions.lean), [Challenge](Challenge.lean), and the [complete source correspondence](SourceCorrespondence.md). The [source manifest](source-inputs.json) binds eight original files to upstream revision `f41f1f9ffa2171550d4bb795862c6170c4f26070`.

## Eight intended exports

All names have prefix `NLA.IV06.`:

1. `eigenvalue_determinant_semantics`
2. `family_and_determinant_semantics`
3. `witness_eigenpairs`
4. `witness_separators`
5. `connected_component_intervals`
6. `four_components`
7. `counterexample`
8. `not_componentBoundConjecture`

[comparator.json](comparator.json) lists exactly those declarations, has no replaceable definition names, and permits only `propext`, `Classical.choice`, and `Quot.sound`. The Challenge is a trusted statement environment with explicit placeholders, and the eventual Solution must never import it.

## Pinned tools and statement checks

Lean is pinned to 4.33.1; LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926`; Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. [The manifest](lake-manifest.json) fixes all ten dependencies. The initial Lake configuration registers `NLA`, `Challenge`, and the future `Solution` library, while the default target remains `Challenge`.

The local statement driver compiles Definitions, Challenge, and a semantic inspector into a **new independent prefix**. To avoid another large cache on the nearly full disk, it reads the ten exact pinned source checkouts and available dependency objects from the MI-22 worktree. It excludes both MI-22 and IV-06 project objects. The unused `Cli` checkout has no generated object directory. This is disclosed development-cache reuse, not a fresh dependency compilation or Linux check. The driver does not run Lake or mutate those caches.

[Fresh commands, pins, hashes and outcomes](reviews/statement-evidence/fresh-checks.json), [the actual semantic inspection](reviews/statement-evidence/reviews-statement-evidence-Inspect.log), and the [independent exact diagnostics](reviews/statement-evidence/exact-checks.json) are retained. Three core definitions pass LeanCert's kernel trust audit and standard-three axiom checks; this does not turn Challenge placeholders into proofs. The initial failed statement attempt is archived as text; the corrections were Lean's reserved lambda identifier and the import supplying the real topology, before any review freeze.

On a normal checkout with the pinned dependencies available:

```
lake build NLA.IV06.Definitions Challenge
```

The retained local cache driver is reproducible in the disclosed development environment:

```
python3 reviews/statement-evidence/run_statements.py
python3 reviews/statement-evidence/check_exact.py
```

The only planned interval computation is the actual strict upper-margin certificate `(-18 : ℝ) < 0`, in explicit LeanCert kernel mode on a singleton. It must be consumed in excluding all three separators. Exact matrix algebra, full-box bounds, eigenvector/determinant equivalence, real connectedness, and the cardinal injection remain mathematical proof obligations. No numerical eigenvalue search or interval subdivision is planned.

Both independent statement reviews are pending. Complete proofs, two independent final proof reviews, actual Linux Comparator/default-kernel replay with controls, an independent operational audit, and a truthful v0.4 `formalization.yaml` are still required before promotion. This statement-only package is not ready for a verification PR.
