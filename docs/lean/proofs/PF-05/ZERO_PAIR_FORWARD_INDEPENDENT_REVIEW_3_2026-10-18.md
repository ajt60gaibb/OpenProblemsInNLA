# PF-05 actual zero-pair forward branch — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026. I authored no PF-05 proof source and made no proof edits. **APPROVE the complete forward implication for the stated actual nonzero zero-pair branch. The full PF-05 equivalence remains separate.**

| Reviewed new source | SHA-256 |
| --- | --- |
| ZeroAlternativeRaw | `b30c914e8b7a3d3a36624b7d7f3ec8ca7842fe97ca6c952e134ede6f121439c5` |
| ZeroAlternativeShear | `28062d8a8bb47359c4235a9db953fdee3df36477b7dc1f6c3047e385c25793b0` |
| ZeroAlternative | `35628aa3cd92cf9ba387262c267e91ce4e0994094f2884193ddf64e1d9ffc760` |
| ZeroPairRigidity | `3e060296c70c4b2840860a4e99f1d2f4d182d6fdbedba79d79f6554fff702614` |

The earlier exact CongruenceTransport, ZeroCanonical and ZeroDirection source reviews remain applicable and are included in this fresh closure. All four additional sources above were read completely against the frozen predicates and retained normalization/operator lemmas.

For two actual factorizations with the same normalized distinguished P,Q pair, `ZeroAlternativeRaw` obtains the genuine finite coordinate change L from the retained rank-three factorization theorem. The distinguished primal P fixes row zero of L; the distinguished dual Q and the actual inverse-dual relation fix column one of L. This gives the asserted four-parameter form, with determinant equal to the off-diagonal multiplier γ. Its nonzeroness follows from the actual invertibility of L. The row/column coordinate conventions retain the factor two in the dual off-diagonal coordinate; no arbitrary finite operator or favorable normal form is assumed.

`ZeroAlternativeShear` removes δ by the actual determinant-one shear `[[1,0],[-δ,1]]`. Direct multiplication gives the exact new parameters α−2δγ and β−δ². If necessary an actual determinant-minus-one reflection changes γ to −γ, giving **strictly positive γ** without restricting which alternative was supplied. The same shared congruence acts on the actual factor families. The inverse-dual formula is then recovered from equality of the actual trace products and rank-three trace separation on the actual transformed primal factors. It is derived rather than stipulated as an extra normal-form premise.

`zeroAlternative_normal_form` permits **every actual alternative factorization** of the same M. Its two distinguished alternative factors are proved nonzero: a zero one would make the corresponding row/column of M vanish, forcing the original distinguished factor to vanish by rank-three trace separation, contradicting P or Q. Their actual trace product is zero because the original pair is P,Q. The retained concrete PSD pair normalization therefore applies to them, with nonzero determinant proved there. Composing that normalization with the shear/reflection gives the required shared invertible congruence and positive γ for the entire alternative family. No alternative normalization or nonzeroness premise remains at this interface.

For the normalized base, actual transformed alternative PSD factors supply the canonical PSD endpoints from the earlier source review. They yield the actual common feasible straight interval. The original rigidity predicate forces the primal direction to be one common scalar; actual rank-three trace separation gives α=β=0 and γ²=1. The independently derived γ>0 then gives γ=1. The two actual canonical maps are the identity on the symmetric base factors. Thus the constructed congruence sends the arbitrary alternative back to the base; its genuine inverse gives exactly the direction of the frozen `UniqueUpToCongruence` conclusion.

Finally `zero_pair_rigid_implies_unique` starts with the **original** M, A, B, selected indices, nonzero selected factors and the actual zero entry. It normalizes that actual pair, transports actual straight rigidity with the same positive common interval, applies the just-proved normalized uniqueness theorem, and composes the base normalization, middle congruence and inverse alternative normalization. This restores the original coordinate system and one shared genuine congruence for both whole families. It does not replace M or prove uniqueness only for normalized factors.

The branch hypotheses are exactly an actual rank-three size-two PSD factorization, one selected pair of nonzero factors with `M i₀ j₀=0`, and actual straight infinitesimal rigidity. Other zero, singular and repeated factors are unrestricted. The conclusion is the actual frozen uniqueness predicate for those original factors. The branch does not cover a selected zero entry whose row or column factor is zero; such rows/columns and the entrywise-positive case require the later case assembly. No reverse uniqueness-to-rigidity implication or full Target is asserted here. The explicit nonscalar-direction theorem also has its literal proved condition: the parameter tuple is not simultaneously `γ²=1, α=0, β=0`; it does not assume non-scalar feasibility as an oracle.

Independent immutable verification passed **16 Lean commands**: all **15 actual local sources** in this branch closure plus a separate consumer. It audits **160 explicit proof declarations**, with **135 theorem/lemma-kind checks**. All pass LeanCert kernel trust and printed transitive axiom checks with closure contained in `[propext, Classical.choice, Quot.sound]`. The generated consumer checks actual private constants directly and generated unnamed helpers transitively. All source hashes match the frozen inputs above and remain unchanged after the audit.

Every local object is rebuilt from immutable snapshots into fresh isolated outputs, excluding campaign project objects; only pinned dependency/core objects are reused. All ten dependency revisions/tracked trees pass before/after. **All seven retained candidate modules** match their original retained lock before and after, including retained modules outside this branch's import closure.

```bash
python3 docs/lean/proofs/PF-05/verification/check-zero-pair.py \
  --top ZeroPairRigidity --evidence-name zero-pair-forward-review-3
```

Exact source snapshots, generated consumer, driver, hashes and raw logs are in [verification/zero-pair-forward-review-3/](verification/zero-pair-forward-review-3/). The result explicitly records `full_pf05_target_proved: false` and `authoritative_linux_comparator: false`. No proof, original page, target, permanent ID or canonical path was changed. This is independent AI-agent source review and local kernel evidence, not external human peer review or actual Linux/Comparator acceptance.
