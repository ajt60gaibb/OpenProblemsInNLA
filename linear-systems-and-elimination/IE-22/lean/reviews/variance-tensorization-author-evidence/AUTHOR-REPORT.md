# IE-22 finite-product variance foundation: author evidence

The 324-line `NLA/IE22/VarianceTensorization.lean` module is complete for the assigned bounded foundation. Final source SHA-256: `bf6ff155ed7976e6d6fd5a4d1c12fed572f7027e9bbfd80ee42dd81530ae565d`.

Author role: Codex AI `/root/ie21_final_correctness`, formalization attributed to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Matthew J. Colbrook retains attribution for the original IE-22 application. This is author evidence, not independent review; the agent's previous nonauthor IE-21 referee role does not make it independent of this new IE-22 module.

The public Gaussian tensorization theorem has exactly the requested form. For every natural dimension `d`, measurable `f : (Fin d → ℝ) → ℝ`, and explicit global bound `∃ C, ∀ x, |f x| ≤ C`, its variance under the actual product of `gaussianReal 0 1` is at most the sum over coordinates of the product expectation of each scalar coordinate-section variance. No Poincare, independence-of-projected-rows, variance inequality, or conclusion-bearing hypothesis is assumed. Dimension zero is covered. The boundedness assumptions ensure that all first/second moments, section variances and displayed integrals are finite, rather than using Lean's default values for nonintegrable functions.

The proof first expands the exact two-factor variance decomposition. It proves variance contraction under averaging by centering in the first coordinate, applying scalar Jensen (derived from nonnegative variance and its second-moment identity), and using Fubini. It then inducts on dimension using the actual measure-preserving `piFinSuccAbove` equivalence and `Fin.cons`; coordinate zero and successor updates are accounted for literally. The generic finite-product theorem works for any probability law on ℝ and specializes to the standard Gaussian. The two resampling lemmas use the same actual measurable equivalence at an arbitrary coordinate, together with `Fin.update_insertNth`; they do not assume a resampling identity.

The eight exported APIs are:

- `bounded_variance_prod_decomposition`
- `bounded_variance_integral_le`
- `bounded_variance_prod_le`
- `bounded_variance_pi`
- `gaussian_variance_tensorization`
- `gaussian_coordinate_variance_integrable`
- `bounded_integral_coordinate_resampling`
- `gaussian_integral_coordinate_resampling`

The three Gaussian APIs use the same measurable/global-bound assumptions. The integrability helper discharges the left-hand integrability needed to integrate scalar Poincare bounds. The resampling helper states exactly `∫ x, ∫ t, f (Function.update x i t) ∂γ ∂π = ∫ x, f x ∂π`. Consumers still need to prove their concrete hinge and squared-partial functions measurable and bounded; none of those application obligations is hidden here.

The final module imports only four Mathlib modules; it imports neither IE-21 nor another IE-22 proof module nor Challenge. The final fresh local build used `/private/tmp/nla-ie22-tensorization-final-htp1drm7`, with no existing project objects on its Lean path. Both the module and all eight explicitly restated helper signatures compiled with zero warnings/errors. All eight transitive axiom closures were exactly `propext`, `Classical.choice`, `Quot.sound`. Full commands, hashes, compiler version and outputs are retained in `fresh-build.py`, `fresh-build.log`, `ExactHelperTypesAndAxioms.lean` and `fresh-build-receipt.json`.

Earlier development failures and the successful six-helper build before the requested resampling addition are retained separately. The final build reused pinned upstream Mathlib dependency objects; it did not rebuild/authenticate remote dependencies. No authentic Linux LeanCert/Comparator run, complete IE-22 resolution or independent review is claimed by this author evidence. The frozen IE-22 boundary and all 31 vendored IE-21 source files remain unchanged. Independent review and the eventual full-problem verification gate remain required.
