# TR-27 bounded algebra implementation: author evidence

Date: 2026-09-22. Authoring agent: `/root/canonical_inventory`. This is author evidence, **not independent proof review or full-problem verification**. Work began after `reviews/statement-freeze.json`, which records both independent statement approvals. Frozen Definitions, Challenge, and NUMERICAL_TARGETS hashes remain unchanged.

The new `NLA/TR27/Algebra.lean` imports only `NLA.TR27.Definitions` and `Mathlib.Tactic`. It contains 18 proved theorems and one linear-map definition with proved linearity. There are no placeholders, custom axioms, native proof shortcuts, or imports of Challenge. Its SHA256 is `ce5694407e1e40b201746dc52897ea05acbb69c27efa6c79bfb700fe070d5134`.

Three complete frozen Challenge signatures are now implemented:

- `integral_quadratic (w : ParameterSpace)` proves `85*(w 0^12)^2 + (8*homogeneousMap w 0 + 9*homogeneousMap w 1)*w 0^12 - 5*(homogeneousMap w 0)^2 = 0`.
- `quotient_semantics` proves the actual linear-map realization, surjectivity, and equality of the zero fiber with `Submodule.span ℂ {center}`.
- `curve_nonzero : ∀ t : Option ℂ, curve t ≠ 0` covers every complex parameter and infinity.

The auxiliary exports are `quotientLinearMap`, `quotientMap_surjective`, `quotientMap_center`, `quotientMap_kernel`, `coordinateIndex_ne_one`, `witnessVector_apply`, `curve_some_apply`, `homogeneousMap_apply`, `homogeneousMap_one`, `homogeneousMap_infinity`, `curve_mem_range_homogeneousMap`, `witnessVector_nonzero`, `curve_three_sum`, `borderCurve_zero`, `borderCurve_nonzero`, and `borderCurve_divided_difference`. The last identity assumes only `t ≠ 0`. The chart identities identify the exact finite and infinity curve vectors with actual points of the homogeneous image; they do not establish the whole-image equality.

The proof uses the explicit right inverse of the quotient map, coordinate identities, polynomial normalization, and exact rational arithmetic. For nonvanishing on the finite chart, coordinate zero forces `t=5/3`, and coordinate one then yields the contradiction `−85/9=0`. Infinity has final coordinate five. No interval certificate or approximate numerical computation is used; LeanCert was not invoked for these algebraic helpers.

Run `python3 reviews/algebra-author-evidence/typecheck.py` from the draft directory (or use its absolute path) to repeat the development-only check with the recorded pinned macOS executable and package cache. It compiles Definitions and Algebra into `/private/tmp/nla-tr27-algebra-build`, then compiles `Axioms.lean`. All three runs exit zero, without warnings. `development-typecheck.log` records the command lines and Lean version. `Axioms.lean` prints the transitive axiom closure of every new declaration; all 19 closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

No shared metadata, README, build driver, frozen statements, or canonical pages were edited in this proof task. The module still requires independent proof review, a clean authoritative Linux build, kernel-trust checking under the full campaign runner, and Comparator against the frozen Challenge before it counts as verification evidence. Geometry, rank lower bounds, and the complete TR-27 target remain unproved by this module.
