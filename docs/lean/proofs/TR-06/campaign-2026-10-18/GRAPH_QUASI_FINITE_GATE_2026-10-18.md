# TR-06: complex point derivations imply genuine local quasi-finiteness

18 October 2026. Author: campaign agent `fr05_statement`. This records an implemented generic G3 support gate. It is an author scope report, not independent approval and not a full TR-06 proof.

## Frozen sources

The sources are new files in `lean-statements/NLA/Proofs/TR06/`; no retained source was edited.

| Source | SHA-256 |
| --- | --- |
| `GraphQuasiFiniteCotangent.lean` | `4b20d9de74b6cb928f2acae9200053dce0e8fd6c8df93bb0b8ce46cbc5b2771b` |
| `GraphQuasiFiniteCharacter.lean` | `38ebd4a90146c4ef273723f4e2ed4bc7d74a5d6e70134a2f20ca310a437667de` |
| `GraphQuasiFinite.lean` | `e20544ae7d674c8161125d000294c6133d8f1e0db6eb9777921b8e091f444970` |

Import `NLA.Proofs.TR06.GraphQuasiFinite`. All declarations lie in `NLA.Proofs.TR06.GraphQuasiFinite`.

## Exact actual-character endpoint

`isUnramifiedAt_of_point_derivations` and `quasiFiniteAt_of_point_derivations` have the same hypotheses:

```lean
{R S : Type*} [CommRing R] [CommRing S]
[Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
[IsScalarTower ℂ R S] [Algebra.FiniteType R S]
(χ : S →ₐ[ℂ] ℂ) (ψ : R →ₐ[ℂ] ℂ)
(hcompat : χ.comp (IsScalarTower.toAlgHom ℂ R S) = ψ)
(hzero : ∀ δ : S →ₗ[ℂ] ℂ,
  (∀ a b, δ (a*b) = χ a * δ b + χ b * δ a) →
  (∀ b : R, δ (algebraMap R S b) = 0) → δ = 0)
```

Their conclusions respectively are exactly

```lean
Algebra.IsUnramifiedAt R (RingHom.ker χ.toRingHom)
Algebra.QuasiFiniteAt R (RingHom.ker χ.toRingHom)
```

The base character and its canonical compatibility remain explicit. The character kernel is the actual prime kernel of the supplied character, not an independently chosen point. Character surjectivity is derived from the complex constants internally. No assumption of reducedness, an already finite fiber, a supplied unramifiedness theorem, real setwise local injectivity, or algebraic Jacobian certificate appears in either endpoint.

## Proof and reusable intermediate gates

`cotangent_fiber_subsingleton_of_derivations` works over a generic target field K. Every K-linear functional on `K ⊗[S] Ω[S/R]` yields an actual S-linear map `Ω[S/R] → K`, hence an actual R-relative derivation by the Kähler universal property. If every such derivation is zero, that functional kills all pure tensors and is zero. Linear-dual separation over a field makes the cotangent fiber a subsingleton. This argument does not infer complex tangent information from real local topology.

`residueCharacterEquiv hsurj` constructs an actual S-algebra equivalence from `(ker(algebraMap S K)).ResidueField` to K. It lifts the actual source map through the prime quotient and residue-field localization; every element outside the actual kernel maps to a nonzero field element and hence a unit. The lift is injective as a field homomorphism and surjective because the original character is surjective. Its S-algebra commutation proves the scalar compatibility used for tensor transport.

`isUnramifiedAt_character_of_derivations` transports the actual zero cotangent fiber through that equivalence. The finitely generated Kähler-module support criterion identifies vanishing residue fiber with absence from support. Mathlib's proved equality of the unramified locus with the complement of Kähler support then gives actual local formal unramifiedness. The finite-type unramified-local-structure instance gives actual local quasi-finiteness. This uses the genuine residue-field/Nakayama theorem, not an assumed converse to a differential statement.

The final complex wrapper equips ℂ with the actual χ- and ψ-induced source/base actions, proves the scalar towers from the explicit compatibility, and restricts every actual relative derivation to its ℂ-linear point derivation. The supplied `hzero` therefore kills all relative derivations, giving the stated algebraic conclusions.

## Exact scope and remaining actual-model obligations

This support gate proves the intended local converse from complex relative point-derivation vanishing. It can be used for the actual finite-type normalized graph algebra and an actual selected coordinate projection after proving that every relative point derivation is zero using its actual radius/coordinate relations and the actual full-rank complex selected projection. That actual instantiation is not contained in these three files.

Uniform global bounds on the resulting graph projection fibers, graph-chart volume bounds, actual positive/finite annular volume, actual annular angular numerator, and the final original intrinsic/ten-export assembly remain separate obligations. In particular, the support gate does not replace full complex tangent information by real local injectivity: the radial cubic example prevents that substitution. It does not assert any polar integration formula or finite Gaussian mean for the actual model by itself.

## Verification, attribution and preservation

`python3 graph-quasi-finite-development/replay.py` reproduces the frozen source checks and four builds in separate replay output. `graph-quasi-finite-development/result.json` records an author replay from exact three-source snapshots into fresh private object output, plus a fresh eight-declaration consumer; package dependency objects are read-only. Every source and consumer uses LeanCert kernel assertions; printed axiom closure is limited to `propext`, `Classical.choice`, and `Quot.sound`. This is local Lean 4.33.1 evidence, not Linux Comparator evidence or independent source approval. The independent verifier is asked to review all three new source bytes and replay them independently.

`graph-quasi-finite-development/preservation-checks.json` checks all 58 retained TR06 modules and both unchanged live/frozen shared statements against their immutable earlier snapshots; all 60 checks pass. The six earlier `UnramifiedDifferential*.lean` and five `HomogeneousGaussian*.lean` gates were not changed. No canonical page, original artifact, permanent ID, registry, comparator, or mathematical target was edited. This gate follows the approved complex algebraic route and reuses Mathlib's Kähler differential, local Nakayama/support, residue-field, and unramified local-structure proofs; it adds no external theorem assumption.
