# TR-06 actual unramified differential gate: implemented API and scope

18 October 2026. Author: campaign agent `fr05_statement`. The six new sources below are frozen after a clean complete six-source replay, each with LeanCert kernel assertions and standard axiom closure. Independent source/kernel review is requested separately; this author report is not independent approval.

| New source in `lean-statements/NLA/Proofs/TR06` | SHA-256 |
| --- | --- |
| `UnramifiedDifferentialAlgebra.lean` | `1ecb84f3f472b58789cfa22b62671d3c8676bca1c4912ca61c02bae25e68fdb2` |
| `UnramifiedDifferentialCoordinates.lean` | `e8f5489c8266cc7b58ed581b3e813e1a719b57b6afb3e503e023814253663155` |
| `UnramifiedDifferentialJet.lean` | `3a8cd24545e245e6fc6f06aad2261e74b82ff0f6869387eb3fc41a3d494b6399` |
| `UnramifiedDifferentialGoodLocus.lean` | `eb4b0162d636a84ea3b49899d01b2a9bcfa2ec398ee14fa71a8d17089b60da14` |
| `UnramifiedDifferentialRealJet.lean` | `3f69735b4c4fa3d4277902f1be1bef8a1782c9c754fb92806105989835244b7d` |
| `UnramifiedDifferentialReal.lean` | `7f727d6887eef2b702703346cc6c1b839e05e952f991fcf2d2b18497316b9c3f` |

## Strong actual-model endpoint

Import `NLA.Proofs.TR06.UnramifiedDifferentialReal`; namespace `NLA.Proofs.TR06.UnramifiedDifferential`.

`exists_ambient_real_derivative_denominator hd hgeneric` has the following literal content, where hgeneric is the retained nonvacuous generic complex identifiability predicate and hd is 0<d:

```lean
∃ P : MvPolynomial (TensorIndex d n) ℂ,
  additionAlgebraHom d n r P ≠ 0 ∧
  ∀ (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀),
    (∀ i, (p i).1 ≠ 0) →
    MvPolynomial.eval (fun q => complexify (pivotSum q₀ p) q) P ≠ 0 →
    Function.Injective (fderiv ℝ (pivotSum q₀) p)
```

Thus the denominator is a genuine actual ambient polynomial nonzero on the actual addition-image algebra, and the conclusion is the genuine real Fréchet derivative in exactly the retained ordered-pivot coordinates. No unramifiedness, derivative-rank certificate, generic-Jacobian assertion, tensor-rank equality, finite-volume or regularity theorem is supplied as an additional premise to this endpoint. The mode used to absorb amplitude is chosen internally as Fin0 using hd. The conclusion holds for every prescribed pivot pattern, every actual nonzero-amplitude chart point and every original tensor format admitted by the hypothesis; no rank/order/size special case is substituted.

`exists_unramified_addition_denominator` separately exposes the actual nonzero t in AdditionImage and the exact canonical formal unramifiedness predicate for R[1/t]→S[1/t]. `exists_unramified_derivative_denominator` gives the actual complex Segre-parameter derivative conclusion. Pointwise versions expose the precise genuine localization/nonzero-character-denominator premises when later gates combine good opens.

## Why the algebraic point derivation is genuine

`point_derivation_zero_of_unramified_away` constructs the actual square-zero lift s↦(χ(s),δ(s)) from an additive map satisfying the literal point-Leibniz identity and vanishing on the whole base. Its denominator has nonzero actual χ-value, hence is a unit in the trivial square-zero extension. Both this lift and the zero-derivation lift extend through the actual source localization. The first-projection compositions agree, and its kernel has actual square zero, so formal-unramified uniqueness makes the localized lifts equal. Their second components force δ=0.

The canonical wrapper derives formal unramifiedness over the original base by composing the original-base localization (itself formally unramified) with the given exact R[1/t]→S[1/t] map. It uses the canonical `Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers t))` action from the retained theorem. The proof uses the equivalent square-zero universal property directly, rather than claiming an unavailable Derivation.localize API.

`pivotSourceHom` is an actual substitution from the retained SegreSource subalgebra of raw factor polynomials into the retained exact-dimensional pivot-coordinate polynomial ring. The amplitude is absorbed in a fixed actual tensor mode. It sends each actual Segre coordinate to the exact `summandPolynomial` and each actual addition coordinate to the exact `sumPolynomial`.

`pivotJet` evaluates those actual coordinate polynomials in the trivial square-zero extension at X_c↦(z_c,v_c). Its first component is actual evaluation; the second is an actual ℂ-linear point derivation (the source interface carries its additive map and proves the exact χ-Leibniz rule). The whole AdditionImage annihilation is proved by polynomial generation from the actual addition coordinate sums, not taken as a supplied tangent condition. The amplitude coordinate is an actual summand pivot; each non-anchor parameter is recovered by the one-mode-replaced actual tensor coordinate, whose polynomial is amplitude times that parameter. Therefore zero on every actual Segre-coordinate jet forces the literal parameter direction to vanish when amplitudes are nonzero.

## Analytic and real bridges

Polynomial induction proves actual smoothness and proves that the second jet component equals the derivative along the actual affine line z+t•v. The actual complex addition derivative killing v then forces every actual addition-coordinate jet to vanish by the chain rule and uniqueness of derivatives. Applying the genuine generic-unramified localization to this actual point derivation proves complex derivative injectivity.

For the real transfer, the complex affine-line derivative is restricted to real t and compared with the complexification of the actual real sum derivative. The retained `sum_complexParameter` identity is used literally. This does not identify real tensor rank with complex tensor rank and does not require any such assertion.

`pivotParameterEquiv q₀` is an actual continuous linear equivalence from retained `OrderedPivotData q₀` to retained `Segre.Parameter ℝ q₀`, flattening amplitude and non-anchor entries. The decoded summands and sums agree exactly, and the chain rule transfers injectivity to the actual retained `pivotSum`. This equivalence is not asserted to be an isometry; no angular operator-norm equality is inferred from it.

Finally, the original generic complex witness supplies an actual identifiable exact-rank tensor. The retained actual character-fiber/localization theorem gives generic quasi-finiteness of the actual addition-image algebra. The retained characteristic-zero theorem gives the genuine nonzero unramified denominator. Choosing its actual ambient polynomial preimage and proving character evaluation equals evaluation at the actual tensor sum gives the stated endpoint, with no residual Jacobian or unramified certificate hypothesis.

## Completed gate and remaining work

This completes the differential portion of G1, including its actual real chart interface. It does not establish the full Target or any missing finite-mean/source correspondence declaration. The actual joint good open still needs to combine the derivative polynomial with the independent finite/properness denominator and original identifiability witness. The actual source-dimensional nonzero-pullback/exceptional-nullity and nonempty real regular-chart work remain G2 obligations. Actual normalized-graph coordinate-projection fiber bounds and finite graph volume remain G3 obligations. Their actual annular volume/numerator inputs must still instantiate the independently implemented G4 theorem. The unchanged intrinsic/shared Target still requires the independently proved semantic/tangent/measure bridge and final assembly.

## Evidence and preservation

`unramified-differential-development/result.json` binds the six final source hashes and successful builds. Logs print standard `[propext, Classical.choice, Quot.sound]` closure and pass kernel assertions. No axioms, admissions, sorry, native decisions or external numerical certificates were added. This is local macOS Lean 4.33.1 evidence, not Linux Comparator evidence.

During development, exact retained modules were imported read-only from the previously fresh 61-source preproof review-2 objects. An agent-specific namespace view uses directory symlinks, so the old worktree and dependency cache were not mutated. `development-helper.py.txt` records those paths; the preproof source/pin receipt records their provenance. All six new modules were replayed in dependency order from the final bytes. Independent reviewers are requested to regenerate their whole immutable import closure.

`preservation-checks.json` verifies all 58 retained module source bytes plus the unchanged live/frozen shared TR06 statements against the immutable preproof snapshot (60 checks, all passing). No retained namespace, license/author header, original target/artifact, canonical page/path, permanent ID, registry, or prior verification was edited. Mathematical attribution remains the retained Colbrook solution and existing George Stepaniants algebraic/analytic foundations; these six new bridge proofs are explicit additions within that approved route.
