# TR-15 independent statement referee 1

**Verdict: APPROVE the complete frozen statement boundary.** No mathematical or semantic correction is requested. This is one independent statement approval; the second independent approval is still required before proof implementation. This report proves no challenge theorem and does not change the canonical status.

Reviewer: agent `solved_statement_inventory`, 12 September 2026. I did not author or modify TR-15's definitions, challenge or numerical specification. I read the full retained canonical README and generated TeX, the complete Colbrook manuscript in Markdown and TeX, the full definitions/challenge/numerical specification/source correspondence, the proposed configuration and the actual pinned library definitions identified below. The two retained source PDFs were checked for immutable byte identity; no visual PDF review is claimed.

## Frozen source and statements

The source revision is `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Statement freeze `reviews/statement-freeze.json` has SHA-256 `302e403878a0ceff29cac2b516a97fbc67ce372f7b8526e0e6c0fe4c6ff9eb69`. I independently checked all **19 frozen project files and six canonical/manuscript source files**, before and after fresh elaboration. All match; every source file also matches its immutable Git blob. No `Proof.lean` or `Solution.lean` exists at this gate.

| Frozen boundary or dependency configuration | SHA-256 |
| --- | --- |
| `NLA/TR15/Definitions.lean` | `63b8767fd19148b269f6e4041d464f0de5dc64cac82e1448fee43115bed55379` |
| `Challenge.lean` | `6778940f8f0f645fc6be0c57f1fb8f67791e0c67c896074651bca9cada491428` |
| `NUMERICAL_TARGETS.md` | `6851bb94fb8f6049980113b4df9a1346bd3ed9549f66dd74b2b1f6a5ee947cd6` |
| `SOURCE_CORRESPONDENCE.md` | `55f3c4505c02f50cdbc8e9a6e9bf8853231b569ccecb79c49f7849cba3b9de67` |
| `comparator.json` | `80d0148e7ddf0a431d6833c3e464cf15424c94767394dd1a0fe93366c8bbb45f` |
| `lakefile.toml` | `7b05a8f2330e66b408ef0e1549f61d94f76bb957b88047833118e9cb40344d97` |
| `lake-manifest.json` | `8d71288432949937d6c64f1175c7a9c7c5389bc261d79dad512ba4c385e97127` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

I additionally checked the [Ding–Qi–Wei primary author PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf), PDF pages 2–3 and 8 for array/generator/contraction/H-eigenpair conventions and page 21 for the final inheritance conjecture. These agree with the retained canonical target. This is a convention/target check, not a new literature or priority search. The primary text distinguishes the stronger associated-matrix hypothesis, which is absent here.

## Fidelity of the complete target

`InheritanceConjecture` preserves every original parameter: all natural `m,q,n` with odd `m ≥ 3`, `q ≥ 2`, and `n ≥ 2`, and every real generating vector of length `qm(n−1)+1`. The lower tensor has order `m` and dimension `q(n−1)+1`; the upper has order `qm` and dimension `n`. Both use exactly the same generating vector. The final theorem is the negation of this full universal implication, rather than a restricted-family statement or an assumed algorithmic/numerical reduction.

The finite-array model is faithful. `generatorIndex` uses the actual sum of zero-based indices and proves its bound; it has no out-of-range fallback. This equals the source's one-based sum minus the tensor order. `lowerTensor` uses only `Fin.cast` to identify equal lengths. I checked Lean's actual `Fin.cast` implementation and its elaborated value: it preserves the underlying index, so it cannot reorder or rescale the generator.

The actual elaborated contraction uses `Finset.sum` over `Pi.instFintype` on **all** functions `Fin (s−1) → Fin N`, then `Finset.prod` over all contracted slots. I read Mathlib's `Pi.instFintype`/`piFinset` definition. Thus every ordered tuple occurs exactly once; cross-term multiplicities are genuine, with no factorial normalization. `prependIndex` correctly maps the zero slot to the uncontracted coordinate and each positive slot to the previous contracted slot. Its totalization at order zero is excluded by every admissible instance.

`IsHEigenpair` uses a real scalar, a real vector unequal to the pointwise zero vector, and every component equation with ordinary natural powers of the **signed** real coordinates. The inspection resolves `Pi.instZero` and `HPow Real Nat Real`, not a norm/absolute-value or other spectral convention. `HasNoNegativeHEigenvalues` is exactly nonnegativity of every real H-eigenvalue; over the reals it is equivalent to absence of a negative real pair. No existence, strong-Hankel, associated-matrix positivity, upper-order parity or spectral-enumeration premise is added.

## Independent numerical and logical reconstruction

My separate `exact_reconstruction.py` reconstructs all ordered index tuples directly from the generator, using exact sparse integer polynomial coefficients. It does not call the author's numerical checker. It confirms all 27 lower tensor entries and 64 upper entries, including one-based/zero-based index agreement.

For the lower contraction, all three coefficient polynomials match the challenge. Independently expanding the four linear-form squares confirms the first component is

`(x₀+x₂)² + x₀² + x₁² + x₂²`.

The three individual coordinate squares ensure strict positivity for every nonzero real vector. The first H-eigenpair equation then forces `x₀ ≠ 0` and `λ > 0`. This supplies the full original lower premise for every real eigenpair; it does not infer a universal statement from sample vectors or assume an eigenvalue classification.

For `(m,q,n)=(3,2,2)` and `h=(2,0,1,0,2,0,−1)`, the generator length is seven in both constructions. At the upper vector `(0,1)`, each of the two component sums has 32 ordered terms and precisely one nonzero coordinate product. The surviving generator indices are 5 and 6, giving `(0,−1)=−1·(0⁵,1⁵)`. This is a nonzero real vector with a negative eigenvalue. These data satisfy all admissibility conditions and negate the actual upper conclusion, hence refute the complete quantified conjecture.

The extra lower-eigenpair existence export is also correctly stated as a conclusion, independent of the conjecture's premise. Substitution of `(1,0,t)` produces eigenvalue polynomial `2+2t+2t²`; the third equation's exact residual is `2t⁴+2t³+3t²−4t−1`. Its values at zero and one are −1 and 2. Polynomial continuity and Mathlib's actual `intermediate_value_Ioo` therefore support an actual root strictly inside `(0,1)`, with no root-isolation assumption or approximate eigenpair. I read that theorem's implementation/signature; the open interval in the challenge is justified. These exact diagnostics and analytic observations assess the statements; their Lean proofs are still required.

All seven registered exports have the advertised scopes: complete lower contraction, explicit upper contraction, positivity for every lower pair, unconditional nonvacuous lower pair, exact negative upper pair, the admissible counterexample, and the full universal negation. No export assumes its numerical target.

## Fresh elaboration and trust boundary

I independently compiled Definitions, then Challenge, then a new statement/instance inspection under a fresh separate prefix. The original project `.lake/build/lib/lean` was excluded from `LEAN_PATH`; clean pinned dependency caches were reused. All three commands exited 0. Definitions produced no warnings. Challenge produced exactly seven deliberate placeholder warnings. This is local macOS Lean 4.33.1, not Linux Comparator verification.

The inspection checks all **18 public definitions**: each depends only on a subset of `propext`, `Classical.choice`, and `Quot.sound`, with no hidden definition hole or custom axiom. The seven Challenge declarations contain precisely the intended `sorryAx` placeholder in addition to standard axioms. Actual instances and full quantified signatures were inspected, not merely inferred from comments. Future Solution must exclude Challenge entirely.

All ten installed dependency repositories are clean and match the manifest revisions. The primary pins are Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Minimal finite algebra and IVT are appropriate. The proposed kernel LeanCert certificate for the actual negative eigenvalue `−1 < 0` must participate in the counterexample dependency chain. No interval subdivision, numerical root approximation, native-trust proof or decorative unrelated certificate is needed.

## Scope and evidence

This review applies the project-relevant statement-fidelity, source correspondence, genuine mathematical-definition, nonvacuity, dependency/reuse and attribution aspects of the requested referee standards. It is an independent agent review, not external human peer review. Final proof review, complete axiom/trust checks and real sandboxed Linux Comparator execution remain required.

Fresh evidence is in `reviews/statement-referee-1-evidence/`. Inspection SHA-256: `6f73ba4f1fbb3c6f2a18da3f1f97c0dad1926e85accf2ebfd3dd2f6acd3dd7ff`. Fresh command record SHA-256: `8b8320333d3e268f894f5c2fb5e683fdf895899a699afd961726e57bdc6afcaa`. Exact reconstruction SHA-256: `9ee4b64623e2dcaf60c8b137b597954f0eaf2f54a1f9447d316e08d5c25f67c6`. The evidence manifest records every review input/log/check, and the freeze confirms no statement or canonical source bytes changed.

The mathematical counterexample remains attributed to Matthew J. Colbrook. Formalization credit remains George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No George email or transfer of mathematical authorship is added. The formal target does not classify all odd-order tensors or address inheritance under an additional positive-semidefinite associated Hankel matrix assumption.
