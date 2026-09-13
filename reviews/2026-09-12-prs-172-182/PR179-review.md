# PR #179 — independent IE-12 mathematical review

**Verdict: PASS on the complete exact-real mathematical target.** No proof or scope blocker found. One nonblocking canonical-PDF pagination defect is recorded below.

**Exact reviewed head:** `7ffdc89f5b686574b7d9d7df1f10cedec62bd02c`.
**Date:** 2026-09-12.
**Reviewer:** independent OpenAI Codex AI agent `/root/audit_spectral_linear`. This is an informal AI-agent mathematical audit, not external human peer review or formal verification.

I read the original canonical IE-12 target, the complete 762-line `linear-systems-and-elimination/IE-12/solution.tex`, and all four submitted Python files before executing any contributor code. I did not rely on submitted AI review verdicts. Direct comparison confirms that the original Problem statement is unchanged and that the publication manuscript's mathematical body from Section 1 onward is identical to the submitted source. Repository and GitHub state were not modified. Line locations below refer to the publication `solution.tex` unless otherwise stated.

## Target, model, and rounding

Theorem 1, lines 106–118, includes every original real nonsingular normalized input, every nonzero right-hand side, all `n≥1`, and all `0<ε<1/2`. Its stronger allowance of singular matrices does not weaken the original claim. The algorithm always returns a nonzero vector, has a deterministic worst-case bound `Cn²ε⁻³`, and achieves A-only backward error at most `5ε/8` with probability greater than `0.997`. These imply the requested `0.99` success and exponent `q=3`.

The rounding in lines 145–198 uses only permitted primitives. The comparison/increment floor loops terminate in `O(1+|Aᵢⱼ|/h)` operations, including negative and integral inputs. The three-Gaussian construction produces a genuinely uniform scalar through the uniform sphere in dimension three. Its zero-denominator branch terminates without rejection and changes the distribution only on a null event. Independent Gaussian triples and fresh filter draws supply the independence actually used. There is no exact-Bernoulli oracle or expected-time qualification.

The deterministic estimate `Σ|Aᵢⱼ|≤n‖A‖F≤n^(3/2)` gives `W≤(2+64/ε)n²≤65n²/ε` and the same total rounding-cost bound. In lines 200–240, the centered rounding entries have support intervals of length at most `h`. The supplied exponential-moment proof, bilinear tail `2 exp(−2t²/h²)`, two `1/4` nets, and factor-two norm approximation are correct. With `h=ρ/(8√n)`, the failure bound is exactly `2 exp((2 log9−32)n)<10⁻³`. No dimension-dependent logarithm has been hidden in this rounding error estimate.

## Weighted-pattern multiplication and total cost

The construction in lines 243–353 is proved directly for the growing integer alphabet; it does not apply a constant-alphabet theorem outside its hypotheses. The terminated signed-unary encoding followed by fixed-length padding is injective, including zero coefficients, leading zeros, and the empty pattern. Enumeration, identifier construction, and tail identifiers fit `O(k4ᵏ)` work/storage without digit extraction or hashing as an algorithmic primitive.

The heavy/light packing count is valid: consecutive greedy light bins have combined weight greater than `k`, there are at most `H+n` light runs, and heavy entries number at most `W_H/k`. Thus `S≤2W/k+n`, while separately `S≤n²`. Encoding costs `O(Sk+n²)=O(W)` for `k≤n`. Heavy coefficients are not expanded in unary.

The shifted recurrence `F(j,(a,s′))=a vⱼ+F(j+1,s′)` uses the already computed next row and gives the exact bin product with zero padding. It costs a constant number of scalar arithmetic operations per table entry; table allocation/initialization and unused direct-address slots are explicitly counted. Forward and transpose preprocessing/products therefore have the claimed `O(W+k4ᵏ)` and `O(n4ᵏ+W/k+n)` bounds. Identifiers are constructed integer indices; their use as ordinary array locations or precomputed circuit wiring requires no real-number digit oracle or advice about the input.

The parameter proof at lines 559–589 covers small dimensions, powers of 16, and arbitrary ε. It yields `1≤k≤n`, `k4ᵏ≤4n`, `ℓ≤39k`, and `T≤10000k/ε²`, all implemented by arithmetic/comparison loops. Consequently the explicitly counted preprocessing and every repeated product sum to

`O(n²/ε)+O((kn4ᵏ+W+nk)/ε²)=O(n²/ε³)`.

No dense Gram matrix or original dense residual is recomputed each iteration. The term lists have at most `n²` entries each, and the catalogue and reusable tables satisfy the asserted `O(n²)` scalar storage independently of ε. Counts hold on all random outcomes and have no conditioning or right-hand-side magnitude dependence.

## Kernel filtering and unchanged-right-hand-side conversion

The rectangular `B=[Q,−c]` has a nontrivial kernel regardless of whether Q is invertible. On successful rounding, `‖B‖²≤545/256<4`. The fresh Gaussian start at lines 361–422 has, with probability greater than `0.998`, kernel component at least `10⁻³` and squared total/kernel ratio at most `10⁹d`. The contraction `I−BᵀB/4` preserves that kernel component exactly.

For high eigenvalues, the retained factor `λ` makes `λ exp(−Tλ/2)` decreasing above `η²/2` because `T≥4/η²`. This bounds their residual contribution by `(η²/2)exp(−Tη²/4)‖g‖²≤(η²/2)a²`. The low part is at most `(η²/2)‖z_T‖²`. This proves the asserted residual bound with no spectral-gap assumption and no extra `log(1/η)`. The orthonormal eigenbasis and kernel vector are analysis devices, not computed inputs. Conditional application for each successful rounded Q is legitimate; the total failure probability is strictly below `0.001+0.002`.

The conversion at lines 448–509 is valid for positive, negative, tiny, or zero α. A successful nonzero augmented vector cannot have `u=0`. The estimate `‖z‖/‖u‖≤(2+ρ)/(1−η)<3` and clamping displacement `|α′−α|≤η‖u‖` give the actual original-data error at most `ρ+4η=5ε/8`. Scaling by `β/α′` works also for negative α′. The explicit rank-one perturbation proves this is exactly A-only spectral-norm backward error; b is unchanged. On unsuccessful outcomes the fallback or clamped branch is still defined and nonzero, with `‖x‖≤8‖b‖/ε`.

## Sources, reproduction, and PDFs

I verified the primary [Dereziński–Nakatsukasa–Rebrova v2 paper](https://arxiv.org/html/2604.16075v2), Definition 1/Lemma 2, §3.1, Corollaries 17 and 25, for the metric, exact-arithmetic setting, and contextual prior cost bounds. I also read Liberty–Zucker's primary [Mailman author manuscript](https://www.cs.yale.edu/homes/el327/papers/mailmanAlgorithm.pdf), especially pages 1–3, confirming the finite-alphabet preprocessing context. The new convergence and product lemmas are self-contained rather than imported from those references.

After inspecting `weighted_matvec.py`, `test_exact.py`, `solver.py`, and `run_experiments.py`, I copied the code to `/private/tmp/nla-pr-179-scratch/code` and ran `python3 -B test_exact.py` there. **All nine exact component tests passed.** The tests compare shifted patterns and both product directions to direct rational calculations and exercise floor, parameter, kernel, and clamping cases. They are finite implementation checks; the universal guarantee follows from the analytic proof. I did not run the floating-point experiments or claim that their prototype establishes the theorem's exact distribution, runtime, or numerical stability.

Using the PDF skill and Poppler, I visually inspected all **12 pages**: both pages of the canonical `problem.pdf` and all ten pages of `solution.pdf`. The manuscript pages, equations, code listing, table, and references are legible and unclipped. The canonical status prominently says Solved. **Nonblocking layout issue:** canonical page 2 contains only the historical “Audit update — 2026-09-10” paragraph and otherwise extensive empty space. A page break before “References and status” would group the reference and historical audit material together on page 2 without altering mathematics. This was reported to the main reviewer for integration.

The canonical resolution accurately limits the result to the stated exact-real entry-access model. It does not claim finite-precision stability, bit complexity, dimension-free black-box convergence, practical speed, or Lean verification. Subject to the main reviewer's separate publication/CI checks, **Solved is justified for the complete original IE-12 target**.
