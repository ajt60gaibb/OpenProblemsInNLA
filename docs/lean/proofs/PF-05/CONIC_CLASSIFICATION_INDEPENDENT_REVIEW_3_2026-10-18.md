# PF-05 actual conic-preserver classification — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no PF-05 proof source and made no proof edits. **APPROVE the following exact conditional classification sources. No full PF-05 Target is claimed.**

| Module | SHA-256 |
| --- | --- |
| ConicDeterminant | `f640f126f051f07ae68c5e7ea4d23fc872d5a57275a384019835889d2a01e514` |
| ConicPositive | `e3a8c8493d29d326dceea70eeb1bd3d00c91fdfef1c42863cd76982d898fe91b` |
| ConicCongruence | `73f46bb8227cece8c2c21f40109ba726095176b41a664ee08488c26768d725d6` |

`ConicDeterminant` assumes exactly that the actual three-coordinate primal operator L sends every real rank-one outer product to a singular matrix. Testing five explicit real vectors gives the five coefficients of the actual homogeneous quartic. Exact coefficient algebra then proves preservation of the determinant form on every symmetric two-by-two matrix, with the explicitly defined scalar κ. In row coordinates `(a,c,b)` the determinant metric is `[[0,1/2,0],[1/2,0,0],[0,0,-1]]`, and the correct operator identity is `L*J*Lᵀ=κ*J`. Its determinant, with det(J)=1/4, gives κ³=det(L)². Thus actual invertibility of L forces κ>0 over the real numbers. No congruence representation or cone-component classification is assumed.

The positive-component argument uses an actual positive definite P whose actual image L(P) is positive definite. The determinant polarization against an outer product is the quadratic form of P on the rotated vector `(-v1,v0)`, which is strictly positive for nonzero v. Determinant scaling gives the corresponding positive polarized value against L(P). A real symmetric singular matrix is PSD or its negative is PSD; the positive polar value excludes the negative case. This proves positivity of every actual primal rank-one image, with zero input handled directly. The P and L(P) conditions are explicit here because invertibility and conic preservation alone would also allow the negative component.

The actual inverse primal map is shown to preserve the conic using determinant scaling and κ≠0, then the same positive-component argument applies with P'=L(P). Actual matrix inverse identities retain the determinant guard. Weighted inverse-dual positivity is derived from the actual trace pairing: its quadratic form on each vector equals a nonnegative quadratic form of an already-proved inverse-primal PSD image. It is not supplied as a global cone-positivity premise.

`ConicCongruence` constructs a genuine fixed 4×3 PSD factorization. Its row factors are the outer products of `(1,0)`, `(0,1)`, `(1,1)`, `(1,-1)`; its column factors are the outer products of `(0,1)`, `(1,0)`, `(1,-1)`. The actual trace-product matrix has the explicit 3×3 submatrix `[[0,1,1],[1,0,1],[1,1,0]]`, whose determinant is two. Together with the three-column rank bound this proves actual rank three; no virtual rank assumption is left open.

The proved primal and inverse-dual positivity makes the L-transformed virtual factors an actual alternative factorization of this same matrix. The earlier actual `zeroAlternative_normal_form` theorem applies to its actual P,Q pair. This call uses the purely algebraic normal-form construction, **not** the rigidity-to-uniqueness theorem or any conic-preserver classification, so the classification is not circular.

The transformed virtual rows are all singular by the supplied conic condition. After the actual normalization, their canonical images remain singular. The row Q forces β=0; the two rows from `(1,1)` and `(1,-1)` then force α=0 and γ²=1. The normal form already proved γ>0, so γ=1. Its actual canonical map is therefore the identity on the virtual spanning family. Cancelling the genuine normalizing congruence gives L equal to the actual congruence operator of its inverse. The actual rank-three row-span identification proves equality of the entire coordinate operator, rather than equality only on the selected factors.

The final wrapper `congruent_of_conic_alternative` returns precisely `Congruent A At B Bt` in the **original factor coordinates**. Its two actual factorizations and ordinary rank three supply positive definite row aggregates. Linearity and the actual primal image relation identify the second aggregate with L applied to the first, discharging the positive-component input internally. Classification supplies one genuine S for all primal factors. The actual trace products and rank-three trace separation then force every original alternative dual factor to equal the same inverse congruence applied to B. No inverse-dual family formula is assumed at this wrapper.

The remaining mathematical premise is explicit: the actual alternative coordinate operator must preserve the whole rank-one conic. These modules classify that situation; the quartic obstruction under rigidity and the subsequent forward-case assembly must prove this premise where the full Target needs it. Actual invertibility and the actual primal image relation are also explicit and are supplied later by the retained full-rank factorization change theorem. No full rigidity equivalence is asserted by this review.

The initial two-support immutable audit passed **11 Lean commands**, checking 163 proof declarations and 128 theorem/lemma kinds over ten actual sources plus a consumer. The complete classification audit passed **23 Lean commands**: all **22 actual local sources** plus a separate consumer. It checks **260 explicit proof declarations**, with **203 theorem/lemma-kind checks**. All actual private declarations are located and checked directly; unnamed generated helpers are covered transitively. Every audited constant passes LeanCert kernel trust, and every printed transitive axiom closure is contained in `[propext, Classical.choice, Quot.sound]`.

Every local object is rebuilt from immutable snapshots into fresh isolated outputs excluding campaign project objects; only pinned dependency/core objects are reused. All source bytes and ten dependency revisions/tracked trees pass before/after. All seven retained candidate proof modules match their original retained hash lock before and after, and all seven are also present as exact frozen sources in the full classification closure.

```bash
python3 docs/lean/proofs/PF-05/verification/check-conic-classification.py \
  --top ConicCongruence --evidence-name conic-classification-review-3
```

Exact sources, consumers/drivers, hashes and raw logs are in [verification/conic-positive-review-3/](verification/conic-positive-review-3/) and [verification/conic-classification-review-3/](verification/conic-classification-review-3/). Both results explicitly record `full_pf05_target_proved: false` and `authoritative_linux_comparator: false`. No proof, original page, target, permanent ID or canonical path was changed. This is independent AI-agent source review and local kernel evidence, not external human review or actual Linux/Comparator acceptance.
