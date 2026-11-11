# TR-06 revised statement review — referee 2

Date: 24 September 2026. Reviewer: independent AI agent `/root/tr06_statement_referee_2`. Phase: independent pre-proof review of the revised complete-target interface. Verdict: **APPROVE the exact revised statement boundary for proof implementation**. This is statement approval only: all ten Challenge declarations still contain deliberate placeholders, and no mathematical proof or Lean-verified status is approved.

I read the actual revised definitions, all ten signatures, numerical target inventory, README, Comparator configuration, incomplete metadata, and elaboration evidence. I then independently reran the development elaboration on these exact bytes, writing outputs only under `/private/tmp/tr06-review2/`. I did not implement the candidate files. My earlier design recommendations and initial requested-change report remain preserved; their two substantive findings are explicitly resolved below.

## Reviewed bytes and independent elaboration

The project is `tensor-computations/TR-06/lean` in the worktree `/Users/ajt253/.codex/worktrees/tr06-formal-verification/OpenProblemsInNLA`.

| File | SHA-256 |
|---|---|
| `NLA/TR06/Definitions.lean` | `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898` |
| `Challenge.lean` | `5706c286e2d184965962c31c01805a4d119696459e5bc6e2f90226587e452fbe` |
| `NUMERICAL_TARGETS.md` | `e3a0b1fd548018a1b7afe60d857ff88cf672a429039d240f63068ae4502e355a` |
| `README.md` | `85f8b768d76749fe1b0c25f0de070efc3dd832a459fb66aad16d014e41d2fb5c` |

`revised-statement-hashes.json` records these and five additional packaging/evidence inputs. `revised-reviewed-source/` retains the reviewed copies. The canonical README and original manuscript still have hashes `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` and `65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`, respectively.

My independent command was:

```
python3 tensor-computations/TR-06/lean/development_typecheck.py \
  --lean /Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages \
  --build-dir /private/tmp/tr06-review2/revised-build \
  --evidence-dir /private/tmp/tr06-review2/revised-elaboration
```

Both modules exited zero under Lean 4.33.1, with matching pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Definitions produced no warnings; Challenge produced exactly ten expected `sorry` warnings. The receipt records unchanged input hashes. I inspected both logs in `revised-elaboration/`. This was a macOS development elaboration using existing package artifacts, not a clean Lake build, Linux sandboxed Comparator run, permitted-axiom audit, or proof verification. LeanCert was unavailable in that local package directory and was not used by this statement-only run.

## Resolution of R2-1: generic-assumption correspondence

**Closed at statement level.** `SourceGenericComplexIdentifiable` now explicitly gives an algebraic exceptional set by a family of complex coordinate polynomials. Its nonvanishing witness is an actual complex exact-rank-r tensor, so properness is relative to the tensor rank locus, not merely the ambient affine space. This is a literal polynomial-equation presentation of the original source assumption. Such a witness also makes the exceptional zero set proper in the rank locus's algebraic closure. Conversely properness there supplies a witness on the rank locus by the defining closure property.

`generic_iff_source` is now a compared theorem requiring equivalence of the convenient principal-polynomial predicate with that source formulation. Neither predicate assumes geometric regularity, nonempty real volume, semialgebraic finite volume, or integrability. The original request for a formal source-assumption bridge is therefore represented in the interface. Its proof is still required.

## Resolution of R2-2: canonical smooth inverse, derivative, volume, and expectation

**Closed at statement level.** The revision supplies the previously absent literal source objects and proof obligations:

- `SourceSmoothChart` defines the smooth embedded input locus independently of any summand branch. Its differentiability parameter is C-infinity, represented by the inner top of `ℕ∞` coerced into `WithTop ℕ∞`. Its chart target is open in the entire identifiable real rank-r set and its ambient differential is injective. `sourceSmoothSet` is the union of those actual chart neighborhoods.
- `SmoothDecompositionChart` adds genuine smooth ordered rank-one summands whose exact sum is the input. The normalized tuple is computed before differentiation in the correct product Frobenius norm.
- `IsLocalAdditionInverse` is an actual `OpenPartialHomeomorph` whose source is open in the entire product of nonzero rank-one tensors. The forward map is summation. Its coordinate neighborhood contains the reviewed point and identifies the branch with the chart summands. Membership in the partial homeomorphism source supplies image membership and both inverse laws; the displayed equality therefore really identifies its inverse near the chosen point. The definition does not pre-restrict source tuples to ones already known to be identifiable.
- `smooth_chart_is_local_addition_inverse` requires this genuine inverse property for every relevant smooth chart. It is a conclusion to prove, not a field or premise supplied to the finite-mean theorem. Its admitted dimension bounds match TR-06.
- `sourceAngular` uses the actual chart derivatives and the inverse input differential onto its range. This is the coordinate definition of the intrinsic differential, with the induced ambient tangent norm. It is not another name for `angularSlope`. The local-addition-inverse theorem identifies the chart branch with Ψ; consequently the operator in this definition is precisely the coordinate representation of `D(p^r ∘ Ψ)`. The comparison with arbitrary C1 charts and with operator norms supplies chart and ordering independence. A second public `HasMFDerivAt` statement is not necessary solely to restate the same coordinate definition, provided all ten advertised statements are actually proved.
- `smooth_locus_correspondence` requires the smooth inverse-chart locus to have full tensor volume, measurability, and equality of source and regular volume. Hence the zero convention for `sourceAngular` at points admitting no smooth branch cannot be used to evade the original singular behavior on a positive-measure set.
- `induced_volume_chart` still requires the nonlinear Euclidean-Hausdorff area formula on the actual embedded charts. Smooth decomposition charts yield the C1 charts covered by that theorem. Together with the full-measure correspondence, this identifies the source measure with induced Euclidean volume, including the exceptional-set restoration.
- `source_model_correspondence` explicitly requires equality of the actual Gaussian normalizations and probability measures and AE equality of the derivative condition number with the metric slope. `finite_angular_mean_source` finally states positive finite source normalization, a probability law, measurability, and finite ENNReal expectation under the source generic-complex assumption.

Thus the ten-declaration package reaches the original mathematical target rather than leaving the last derivative/law conversion in prose. The initial five-declaration package lacked this explicit boundary; the revision addresses that finding rather than merely changing documentation.

## Other fidelity and nonvacuity checks

The previously approved concrete aspects remain intact: real and complex tensor coordinates are distinguished; nonzero rank-one summands and exact rank are explicit; uniqueness concerns tensor summands modulo permutations rather than scaled factors; all analytic norms are Euclidean; scalar division at zero is confined to a ratio with an injective differential; angular distance uses an ENNReal infimum with actual decompositions; the slope excludes zero input distance; and the Gaussian coefficient is exactly one half.

The expected dimension is not silently assumed to be actual dimension. Positive-volume, smooth-chart, and normalizer conclusions require proving the dimension bridge. No additional finite angular integral, finite graph volume, real regularity, or probability hypothesis is introduced. The ordinary condition number, independently sampled summands, format-uniform bounds, and higher moments remain outside the claim.

The comparison configuration lists all ten declared targets exactly, leaves replaceable definition names empty, and permits only `propext`, `Classical.choice`, and `Quot.sound`. The inspected incomplete metadata reports no completed target and no Comparator result. Formalization credit and original mathematical attribution remain appropriate, with no new contact email.

## Remaining limitations and required proof review

There are no outstanding pre-proof statement changes from this reviewer for these exact mathematical bytes. All ten statements remain unproved. In particular, the semialgebraic finite-volume theorem, projection/dimension arguments, real regularity from generic complex identifiability, nonlinear area formula, conic polar integration, and all source bridges still require kernel-accepted proofs. The symbolic Gaussian integral is only the final analytic factor and cannot substitute for them.

This approval authorizes proceeding with proof implementation under the agreed workflow. It does not approve a Solution, a final proof path, an axiom audit, a reproduced Linux verification, a completed formalization PR, or promotion of TR-06 to Lean verified. Material changes to the reviewed definitions or theorem signatures require renewed byte-specific statement review; subsequent final proof review must independently inspect the complete implementation and actual mechanical evidence.
