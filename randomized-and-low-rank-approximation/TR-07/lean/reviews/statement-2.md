# TR-07 independent statement review 2

**Phase:** pre-proof statement boundary.  
**Reviewer:** OpenAI Codex AI agent `/root/environment`.  
**Independence:** I did not author the definitions, Challenge, numerical-target record, or proposed proof implementation. I inspected the files directly and performed my own checks. This is an AI review, not human peer review or source-author endorsement.  
**Verdict:** **APPROVE the statement boundary at the hashes below.** This approves fidelity of the mathematical target, not existence or correctness of its future proof.

## Reviewed source and exact boundary

The repository base is `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
I read the canonical README, the complete `solution.tex` (not merely its Markdown pointer), `docs/lean/REVIEW.md`, and the actual Lean declarations and configuration. Paths in the first three rows are relative to the parent TR-07 directory; subsequent paths are relative to this Lean project.

| File | SHA256 |
| --- | --- |
| `README.md` (canonical problem) | `1f2b4c9bfd606f49d2c522483a7375cff104744e7a540db1613bb01f91a281d0` |
| `solution.tex` (complete informal proof) | `207eb87c6b47d3a3a1a529c49b7c5a4dcaf099a942d60fdc1b9b5e3285aae7a0` |
| `solution.md` | `307e8b419a4eb453e789120d86e1344b2aecaf8a8ce759f87d9585a470496fee` |
| `NLA/TR07/Definitions.lean` | `d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233` |
| `Challenge.lean` | `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc` |
| `NUMERICAL_TARGETS.md` | `4780404e41c13668ee57f7c4cff51a4bc9a09fbe1f7ea1f30b6fa936fd7c7a08` |
| `comparator.json` | `019d6a019798a06088b14ddf2a2a7dc0e64b90d03b7d4afbf3062f04da6825b7` |
| `lakefile.toml` | `96cc638603378e99856c50d6ee493e0ef6032a556613a80e2bf2a2b8777bd78e` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lake-manifest.json` | `b1c95fe3e2259153b5659f36de95b6508c973d39ccc23124772a334650c3a19c` |

The canonical source and complete informal proof hashes also agree with the named base revision. The advertised declaration is exactly
`NLA.TR07.random_column_subsets : NLA.TR07.SolvesTR07`.

## Fidelity, quantifiers, and nonvacuity

`SolvesTR07` quantifies over every fixed natural sparsity `s >= 2`, every finite real `C >= 1`, arbitrary dimension sequences `r,n`, arbitrary deterministic real matrix sequences, and every positive real threshold. It contains the original aspect and redundancy limits and `r k <= k`. There are no support-intersection conditions, random-matrix hypotheses, restrictions on signs, or exclusions of repeated columns.

The explicit `r k <= n k` is the domain condition necessary for the original uniform subset experiment. Eventual rather than universal signed sparsity accommodates dimensions `k < s` and permits arbitrary initial matrices. This enlarges the scope instead of rendering it vacuous through impossible sparsity at dimension zero.

For example, for any fixed `s >= 2`, the sequences `r k = k`, `n k = k^2`, and `C = 1` satisfy the dimension and limit hypotheses. For every `k >= s`, all columns may be the same vector with ones in its first `s` coordinates and zeros elsewhere; initial matrices are arbitrary. Thus the hypotheses describe an actual nonempty class. This is an explanatory mathematical nonvacuity check, not a separately formalized example.

Real division by zero gives `k / 0 = 0`. It does not evade the target: convergence of `k / r k` to `C >= 1` forces `r k > 0` eventually. An eventual upper bound on this ratio then forces `r k` to tend to infinity. Combined with `n k / r k` tending to infinity, this gives `r k / n k -> 0`. These deductions remain obligations of the proof; they are not additional hypotheses.

The target is precisely the original asymptotic statement, source Corollary 1.2. Source Theorem 1.1 additionally proves an exponential finite tail for a positive fraction of small singular values. Omitting that stronger auxiliary conclusion does not omit part of the original problem. The numerical-target record accurately limits the advertised scope to the full original asymptotic conclusion.

## Euclidean norm, infimum, and probability audit

I checked the imported `EuclideanSpace` definition: it is `PiLp 2`, not the ordinary function-space supremum norm. Both the selected coefficient space and `selectedAction` output therefore have the required Euclidean norm. `selectedAction` is the literal matrix-vector product for the selected column-index subtype. It is not a compressed or favorable subspace surrogate.

`smallestSingular` takes the infimum over every unit vector in that selected coefficient space, matching the canonical definition. For a nonempty selected index set, the unit sphere is nonempty (a coordinate unit vector suffices), and its image consists of nonnegative real norms, hence is bounded below. Consequently the conditional real infimum has the intended meaning. For the empty selected set the unit sphere is empty; the imported real order implementation has `Real.sInf_empty : sInf (emptyset : Set Real) = 0` (`Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`). This affects only an eventually excluded sample size and cannot manufacture the asserted limit. A proof using conditional-infimum lemmas must still supply their actual side conditions.

`subsetTail` enumerates `Finset.univ.powersetCard r`. I checked the library's membership, cardinality, and nonemptiness specifications: these are all subsets of the column-index set with cardinality exactly `r`, with total cardinality `Nat.choose n r`, and the family is nonempty when `r <= n`. Thus its ratio is precisely the uniform unordered subset probability. Different indices with equal column values remain different sampled choices. The strict tail event is correctly `eta < smallestSingular`, not its non-strict variant.

## Proposed proof route and outstanding proof obligations

I separately checked the revised regularized route in the numerical record for mathematical coherence. With `D_i = p_i + 1/k`, the proposed signed transition, including its absorbing zero state, has conditional mean `Sigma * D^(-1) * v / s`. No sign symmetry or Euclidean contraction of the nonsymmetric filter is used. The conjugate symmetric filter bound has trace factor `trace D = s+1`, consistent with the stated residual bound and increased choice of `L`.

For `ell <= k`, the displayed reservoir inequality follows from the elementary hit bound and `1 + ell*p <= 1 + k*p`. After its one-half coin, the nonzero mass dominates the stated conservative ideal-kernel factor; the fixed zero mass also dominates the ideal zero outcome. The record correctly requires domination of the unnormalized successful kernel rather than claiming that conditioning on all hits preserves the ideal path law. The conservative choices of `L`, `b`, `a`, and `rho` are coherent with the bias, variance, and witness-count estimates.

The deletion-number substitution and polynomial tail can prove the original asymptotic result, but none of these descriptions is a Lean proof. The final review must inspect the simultaneous-witness inequality, bounded-difference variance bound, collision repair, and equal-fiber transfer to the exact `powersetCard` ratio, together with all limiting and infimum bridges. In particular, an ideal reconstruction oracle or a favorable-event assumption would not satisfy this boundary.

## Independent mechanical checks and remaining gates

I independently ran `lake build NLA.TR07.Definitions Challenge` using Lean 4.33.1 and the pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. It completed successfully with 2381 jobs and only the deliberate `Challenge.lean:6:8` placeholder warning. I also read the author's `verification/statement-build.log`; it records the same intended outcome. The Challenge placeholder proves no mathematics.

I independently invoked `tools/lean/harness.py.validate_project` on this project. It passed. The Comparator configuration names distinct `Challenge` and `Solution` modules, exports the full target, has no definition holes, and permits only `propext`, `Classical.choice`, and `Quot.sound`. The manifest uses immutable dependency revisions and the contained package directory.

No proof bodies were reviewed or approved in this phase. Final independent proof review, transitive axiom checks, and the fresh Linux sandboxed Comparator/kernel run remain mandatory. This report does not claim Lean-verified status. A change to the reviewed mathematical definitions or Challenge signature reopens this statement review; a later proof-route revision must be assessed on its own actual content.
