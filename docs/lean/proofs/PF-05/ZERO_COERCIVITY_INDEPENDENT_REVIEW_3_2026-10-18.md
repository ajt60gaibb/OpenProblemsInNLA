# PF-05 congruence, canonical zero direction and coercivity — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no PF-05 proof source and made no proof edits. **APPROVE the following exact support modules. Full PF-05 remains unproved at this checkpoint.**

| Module | SHA-256 |
| --- | --- |
| CongruenceTransport | `49dcd6e2ac47a2f1b75f5852470f704d0685b9624155db92467e8af3f4391fbd` |
| ZeroCanonical | `1cbe237999b668cd1a33cfa195bab1fce46b06e216605a1beaf061f06c73ddf1` |
| ZeroDirection | `9e0829b2605550a88530d1e32abde83821c55c314a7b490f6fa04e65716cf001` |
| PositiveCoercivity | `03233e9c5775dd8b10eef9f49cf42b88ea18756e0df84548248a01671098a7f3` |

`CongruenceTransport` defines precisely the existential congruence relation used by the frozen uniqueness predicate: the same real invertible S acts by `Sᵀ A S` on every row factor and by `S⁻¹ B (S⁻¹)ᵀ` on every column factor. Applying S then T composes as S*T on both families. The inverse, cancellation and symmetry arguments retain the nonzero determinant guards that make the nonsingular matrix inverse genuine. Reflexivity, symmetry and transitivity have the actual shared witnesses and multiplication order.

Straight-line rigidity transport pulls an actual feasible direction back by S⁻¹. The retained congruence lemma preserves the literal trace derivatives, real symmetry, and the same common PSD interval. Cancellation recovers the original base families. Applying the original rigidity property supplies one scalar for all row and column indices; pushing forward by S and linearity supplies that same scalar on the transformed families. This is transport of actual straight segments, rather than an inference from curved congruence paths.

`ZeroCanonical` gives literal symmetric two-by-two formulas for the primal alternative, its trace-dual inverse, and the proposed first-order directions. Direct trace calculations retain the off-diagonal weight two. The inverse-dual and endpoint identities require exactly γ≠0. The primal direction's endpoint at time γ⁻² is the diagonal congruence of the actual primal alternative; the dual endpoint at time one is the corresponding diagonal congruence of the actual dual alternative. These are equality proofs in the actual matrix coordinates, not determinant-only tangent tests. PSD convexity then gives every point on the closed segment to each PSD endpoint. Singular, flat, rank-one and zero factors require no exception.

`ZeroDirection` assumes that these actual canonical alternatives are PSD, then constructs the **single uniform interval** `0≤t<min(1,γ⁻²)` for the entire family. γ can have either sign; γ≠0 makes γ⁻² positive. Both segment bounds and all trace derivatives satisfy exactly the frozen `FeasibleDirection` definition. Positive-time exact factorization is not imposed.

The scalar-parameter theorem is proved from the actual rank-three factorization. If the primal direction equals d times every row factor, its unchanged bottom-right component forces d=0: otherwise all row factors have zero bottom-right entry, contradicting actual rank-three trace separation against the fixed bottom-right matrix unit. The remaining top-left equations are trace orthogonality to the single symmetric matrix with coordinates `(-(γ²-1), α/2, β)`. Actual trace separation forces that matrix to vanish, giving γ²=1, α=0 and β=0. Applying rigidity to the constructed feasible direction derives these parameter constraints without assuming a nonscalar direction. The result correctly leaves the sign γ=±1; it does not incorrectly force γ=1.

These zero modules remain conditional on the stated canonical form and actual PSD alternatives. They do not yet normalize an arbitrary alternative factorization into this form, finish a global uniqueness implication, or prove the reverse rigidity implication. Those conditions must be discharged by later source constructions, rather than read as already-proved parts of the full Target.

`PositiveCoercivity` assumes an actual real two-by-two positive definite P. Its computed constant det(P)/trace(P) is strictly positive. The identity `trace(P)*qform(P,v)-det(P)*||v||²=||P*v||²` follows by exact two-coordinate algebra and gives the claimed lower quadratic-form bound after division by the positive trace. Applying it to the two actual columns of an arbitrary S bounds the sum of its four squared entries by `trace(Sᵀ P S)` with that same constant. Each entry bound follows by nonnegativity of the other three squares. No inverse, spectral lower-bound oracle, compactness or closed-orbit hypothesis is used. Positive definiteness of P is essential and explicit; this module supplies quantitative bounds for a later argument, not a closed-orbit or full rigidity theorem.

Independent immutable verification passed **11 Lean commands**: ten actual local sources plus a separate consumer. It audits **147 explicit proof declarations**, including **119 theorem/lemma-kind checks** and eight actual private constants (seven theorems, one definition). All pass LeanCert kernel trust, and every printed transitive axiom closure is contained in `[propext, Classical.choice, Quot.sound]`. The new modules' exact hashes match the frozen inputs above.

All local objects are rebuilt from immutable snapshots in fresh isolated outputs, excluding campaign project build objects; only pinned dependency/core objects are reused. Source bytes and all ten dependency revisions/tracked trees remain unchanged before/after. Checks of **all seven retained modules**, including those outside this import closure, match the retained candidate lock before and after.

```bash
python3 docs/lean/proofs/PF-05/verification/check-zero-coercivity.py \
  --top CongruenceTransport ZeroDirection PositiveCoercivity \
  --evidence-name zero-coercivity-review-3
```

Exact snapshots, generated consumer, driver, hashes and raw logs are in [verification/zero-coercivity-review-3/](verification/zero-coercivity-review-3/). The result records `full_pf05_target_proved: false` and `authoritative_linux_comparator: false`. No proof, original page, target, permanent ID or canonical path was changed. This is independent AI-agent source review and local kernel evidence, not external human peer review or actual Linux/Comparator acceptance.
