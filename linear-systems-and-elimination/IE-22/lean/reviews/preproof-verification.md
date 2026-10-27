# Independent IE-22 pre-proof review

Reviewer: OpenAI Codex AI agent `/root/verification`, 23 October 2026. I authored no IE-22 implementation. **APPROVE the frozen three signatures and mathematical route; no changes requested.** This approves implementation, not a completed theorem or canonical promotion.

Reviewed packet hashes:

- `CONTRACT.md`: `7e7224aabf0514c1a66cf74e0892b9a9e5a979dbb1b85862d4abfa3736ad94fd`
- `Challenge.lean`: `bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79`
- `INPUT_LOCK.json`: `26fe6dce1658d183be3629094b83ea58e3c11aeb721566c4dd2711372906aad5`

All 32 frozen originals independently match their locked SHA256, size, and Git bytes at published base `5487945e5a72abd952b0c89915915de8cc9b3e65`. These include the immutable registry/path, canonical README/TeX/PDF, manuscript, actual shared definitions, reviewed statement, and historical incomplete project. The historical `IE22.full_result` is an axiom and its `SupremumConverges` omits ambient dimension divergence; neither is imported into the reviewed boundary. The live reviewed Target retains the canonical two clauses and the genuine matrix extremum.

`SubsingularSquared` takes the actual infimum over every real unit direction and all row subsets of cardinality `floor(θm)`. `Extremum` takes the actual supremum over all real unit-row matrices, with the exact square-root normalization. `UniformUpper` puts dimension/aspect thresholds after the requested error and before every positive dimension pair. The first proposed endpoint is stronger than this upper clause because its dimension threshold works for every positive row count. The witness endpoint gives a real unit-row matrix beyond each pair of thresholds. Together, nonnegativity and square-root transport imply the literal `NLA.Statements.IE22.Target`, including every smaller real constant. For negative constants, nonnegative matrix energies already preclude the eventual upper property. For nonnegative smaller constants, choose a squared witness gap that separates the square roots. The proofs must establish the nonempty bounded infimum/supremum domains; default values cannot supply these conclusions.

The upper route is mathematically valid without Gaussian Poincare. For centered joint Gaussian variables, subtracting `(Cov(X,Y)/Var(X))*X` gives a genuine independent residual when `Var(X)>0`; its marginal need not equal Y's. Cauchy-Schwarz, `Var(f(X)) ≤ E[(f(X)-f(EX))²]`, and the Lipschitz bounds yield `|Cov(f(X),g(Y))| ≤ Lf*Lg*|Cov(X,Y)|`. Zero variance is handled separately. The hinge has Lipschitz constant `2√t`. The actual retained covariance spectral bound and finite Gram Cauchy-Schwarz give the stated variance rate `4t/√(r+1)`. This slower rate suffices: fix a finite mesh and sufficiently large fixed r, then take n sufficiently large. Markov's energy bound limits the relevant trimming dual to `[0,4/(1-θ)]`; norm concentration and finite union bounds leave positive probability. Projected rows are never assumed independent. The source's stronger explicit rate is outside these signatures.

The lower route is also valid. Normalizing a standard Gaussian with a unit fallback at zero yields actual unit rows. On radius squared/n at least one half, the hinge discrepancy is bounded by `2 Z² |radius²/n-1|`; fourth-moment Cauchy-Schwarz gives the claimed vanishing expectation bound. On its complement the discrepancy is at most the hinge threshold. This works uniformly for all unit directions and needs no independent radius/direction assumption. For a fixed sufficiently large n, compactness supplies a finite direction net; independent bounded hinges, Chebyshev, and a finite union bound give simultaneous control once m is sufficiently large. The `2n` Lipschitz extension controls all directions. The finite trimming dual lower bound then controls every retained set and hence the actual infimum. The floor costs at most `a²/m`. This yields exactly the witness quantifiers, without a concentration oracle, Haar identification, or an IE-21 theorem premise.

Fresh verification used Lean 4.33.1 with ten independently checked clean dependency pins. The four-module signature scaffold compiled from independently copied frozen source; its three deliberate holes produced three expected warnings. I additionally compiled the reviewed statement and a definitional equivalence check between reviewed and live Targets. A fresh LeanCert kernel consumer explicitly rejected all three placeholder declarations with `sorryAx`. These are statement and rejection controls; they prove none of the mathematical endpoints. No Linux/Comparator acceptance or full Target proof is claimed.

Reproduction:

```sh
python3 reviews/2026-10-23-solved-lean/ie22-next/check_scaffold.py --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages --output /private/tmp/nla-ie22-verification-preproof-fresh
python3 reviews/2026-10-23-solved-lean/ie22-next/check_verification_preproof.py
```

Use a fresh output directory for the first command. Machine evidence is in `PRE_REVIEW_VERIFICATION.json` and `verification/verification-preproof/`.
