# PR #169 — independent MI-26 proof and fidelity review

**Verdict: PASS.** No mathematical, statement-fidelity, or proof-source trust blocker found. The formalization gives a complete negative answer to the original MI-26 assertion. Authenticated current CI and integration are separate gates owned by the main reviewer; this report does not claim a local Lean rerun.

**Exact reviewed head:** `38122892d2d6e6e0093a381dbfe2fbae026ac15b`.
**Date:** 2026-09-12.
**Reviewer:** OpenAI Codex AI agent `/root/audit_spectral_linear`, independently assigned proof, functional-calculus, and witness review. This is AI-agent review, not external human peer review.

I read the complete actual `Definitions.lean`, `Proof.lean`, `Challenge.lean`, and `Solution.lean`, configuration and dependency pins, original canonical statement and informal proof, and the repository's Lean promotion/referee policy. I independently reconstructed the witness with Python `fractions.Fraction`; submitted review verdicts were not evidence. No repository edits, Git mutations, submitted code execution, or remote mutations were performed. Lean source locations below are relative to `matrix-inequalities-and-norms/MI-26/lean/`; Definitions and Proof are in `NLA/MI26/`.

## Exact target and functional calculus

- **Function class and quantifiers:** `Definitions.lean:26–27,44–50` retains all positive dimensions, arbitrary complex PSD matrices, and real-valued functions concave on `[0,∞)` with `f(0)≥0`. The two complex unitaries are existentially quantified after the inputs. No continuity, monotonicity, global nonnegativity, commutation, or invertibility premise is added. `Proof.lean:25–39` proves that `ConcaveOn` is exactly the displayed scalar Jensen inequality, including both endpoint weights. The original target at revision `5adea969c17391693978ada2674d25bb5c3daeb1` is preserved.
- **Half-line representation:** Using total functions `ℝ→ℝ` introduces no restriction: any function on the nonnegative half-line extends arbitrarily to negative arguments. `Proof.lean:51–62` proves that two such extensions give identical matrix functions on every PSD input, using the actual nonnegative eigenvalues. Restriction and extension therefore preserve the original assertion. This argument does not require endpoint continuity.
- **Actual spectral equality:** `Definitions.lean:32–34` uses Mathlib's genuine real `cfc` in the complex matrix algebra. `Proof.lean:42–49` obtains the full unitary spectral formula from `hA.cfc_eq f`, with no continuity hypothesis. I read the exact pinned [HermitianFunctionalCalculus source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean), supplied by the main reviewer through GitHub's contents API. Lines 50–69 construct the spectral star-algebra homomorphism; 91–125 prove its identity/spectrum properties; 132–149 identify it with generic CFC. In particular, line 147 proves continuity of the restriction to the finite spectrum. Thus the generic CFC's fallback value for inadmissible arguments is not being mistaken for a spectral value, even for functions discontinuous at zero on the half-line.
- **Polynomial bridge:** `Proof.lean:64–70` derives `functionalCalculus witnessFunction A = A−A²` for every Hermitian matrix using `cfc_sub`, `cfc_pow`, and `cfc_id'`. The scalar identity and square are continuous, and the actual Hermitian/self-adjoint hypothesis is supplied. `witnessImage` is only a numerical target: its equality to genuine CFC at `P+Q` is proved at lines 118–124. No candidate spectrum or polynomial matrix is substituted for the target definition.

## Independent witness arithmetic and all-unitary exclusion

For `P=diag(1,0)`, `v=(3/5,4/5)`, `Q=vv*`, and `w=(1,−2)`, my independently written exact arithmetic gave

```text
v*v = 1,       P² = P,       Q² = Q,
P+Q       = [[34,12],[12,16]] / 25,
(P+Q)²   = [[52,24],[24,16]] / 25,
H=f(P+Q) = [[−18,−12],[−12,0]] / 25,
Hw = (6/25,−12/25),          w*Hw = 6/5.
```

The scalar concavity proof at `Proof.lean:73–84` uses the exact Jensen gap `θ(1−θ)(x−y)²≥0`. The PSD proofs at lines 86–100 express both matrices as `vv*`, valid over the full complex field. Lines 102–124 prove the projection identities and actual CFC values `f(P)=f(Q)=0`; lines 126–155 prove the nonzero vector and positive quadratic form. No normalization of `w` is required to disprove PSD.

The pinned [Order source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/Order.lean), lines 48–58, defines the scoped matrix order exactly by `A≤B ↔ (B−A).PosSemidef`. The project activates that scope in Definitions, Challenge, Proof, and Solution. At `Proof.lean:157–170`, arbitrary complex unitaries `U,V` conjugate zero to zero, so the proposed inequality would make `−H` PSD. Its quadratic form at the actual complex vector `w` is `−6/5`; taking the real part contradicts positivity. This excludes **every** complex-unitary pair, not merely real orthogonal or selected matrices. Lines 172–176 instantiate the full universal conjecture at dimension two and derive its negation with every premise proved. The seven Solution declarations match the seven Challenge signatures.

## Trust evidence and limits

The only `sorry` terms are the seven intentional, separate Challenge placeholders. Solution imports Proof, which imports Definitions; neither imports Challenge. I found no proof-side holes, custom axioms, native proof mode, unsafe declaration, custom elaborator, or external execution command in the actual project proof source. The sole LeanCert computation, `0<6/5` at `Proof.lean:138–139`, explicitly selects kernel mode and is consumed in the final contradiction. Both Proof and Solution set kernel trust and request assertions/axiom output for all fifteen internal/public declarations. The retained raw `verification/proof-build.log` reports only `propext`, `Classical.choice`, and `Quot.sound`; I inspected those entries without treating the submitted PASS label as evidence. Comparator lists all seven public exports, no replaceable definitions, and only those three permitted axioms.

The project pins Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Direct Git comparison shows no change to actual proof/definition/interface files or configuration pins between the README's immutable proof revision `81176af27e570b59ba1e1a0745e28944e7d57c03` and the reviewed head.

I did not rebuild Lean or authenticate current CI artifacts; the main reviewer owns those mechanical checks. The source and mathematics support promotion once that separate gate is satisfied. The optional positive-definite variant is outside the seven formal exports, and the narrower globally nonnegative function class is not refuted; the README accurately states both limits. Mathematical authorship remains Matthew J. Colbrook's, with George Stepaniants credited for the Lean formalization and AI assistance disclosed.
