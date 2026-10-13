# MF-03 orders one through fifteen: pre-proof contract

## Exact proposed theorem

In a new `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` module, namespace
`NLA.Proofs.MF03`:

```lean
theorem target_through_fifteen :
    ∀ m : ℕ, 1 ≤ m → m ≤ 15 →
      (∃ P Q : Polynomial ℂ,
        NLA.Statements.MF03.ReducedPadeRepresentation m P Q) ∧
        ∀ P Q : Polynomial ℂ,
          NLA.Statements.MF03.ReducedPadeRepresentation m P Q →
          ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
            Q.eval z ≠ 0 ∧
              ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ)
```

This is the exact positive-order clause of the frozen `Target`, with the
additional hypothesis `m ≤ 15`. It neither claims nor implies the all-order
`Target` without a further theorem covering `m > 15`.

## Mathematical assembly

For a fixed order `k` from 2 to 15, the existing `FiniteXX` module supplies a
specific pair `P₀,Q₀` and proves both
`NormalizedPadeRepresentation k P₀ Q₀` and the closed-disk pole-free bound
for that pair. The pair constants are private, but the public theorem types
carry them, so Lean may infer them as arguments to a generic helper.

Apply `normalized_exists_reduced k P₀ Q₀` to obtain `Pᵣ,Qᵣ` with
`ReducedPadeRepresentation k Pᵣ Qᵣ`; this proves the existential conjunct.
For arbitrary reduced `P,Q`, apply `disk_bound_for_every_reduced_pair k P₀ Q₀`
to the normalized certificate, disk certificate, and tested reduced pair.
The transport theorem proves both `Q.eval z ≠ 0` and the bound at every
`‖z‖ ≤ 3`. No uniqueness of the polynomial pair or direct coprimeness proof
for the certificate pair is needed.

At order 1, use the existing `order_one_target_clause`, which already proves
both conjuncts. Finally, `1 ≤ m ≤ 15` gives one of the fifteen exact natural
number values, so finite case analysis dispatches to these clauses. All
endpoints, notably orders 1 and 15 and the closed disk boundary, are included.

## Source binding

SHA-256 hashes at pre-review time:

| Input | SHA-256 |
| --- | --- |
| `Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |
| `Proofs/MF03/Transport.lean` | `902e6c7caf52f462d2bc11fcdf713306f69d67d8da0a159b01713ae31fc6cb66` |
| `Proofs/MF03/OrderOne.lean` | `924c8437e430808f183ff104ee01ba9a1771ccf892a4bb9c37e26ad7c902ca48` |
| `Proofs/MF03/Finite02.lean` | `d1127741afc7ec96469d2a9d6e6c4f6be08d3e1e49cf7bb807760ffc2119097e` |
| `Proofs/MF03/Finite03.lean` | `45ad66cf9ea996dd5ce1a8de884659fac739215c9db2f701ff9ae7e9a66af30b` |
| `Proofs/MF03/Finite04.lean` | `97baa4b71888cb97a6116e26a1d5f1a7d631611b0969a68e80b7f325a5287ee7` |
| `Proofs/MF03/Finite05.lean` | `bc6d2219c84438846b9b6c081b2d9332931c15e9047781560b713a1611545181` |
| `Proofs/MF03/Finite06.lean` | `d8acae03b23c3bebd8309ae9da25b2ac261ba52e5fea41cbfa56ad12b6313a4c` |
| `Proofs/MF03/Finite07.lean` | `5938ae3bf906a1835b0cce737ce5a427465a1255ebd43c757c821248b57a8e21` |
| `Proofs/MF03/Finite08.lean` | `ee431488e3d090efdc4db47fdbe76ee96fdf388a92445f1fda719da78a8e2979` |
| `Proofs/MF03/Finite09.lean` | `5beb2f01343aa7aa5bdf22242498181aa72889b6b92a1fb99f44a42cb9d5c871` |
| `Proofs/MF03/Finite10.lean` | `54742c4fddd08254768482620523e9e141ba49fabaf9344ee7247d66b127c835` |
| `Proofs/MF03/Finite11.lean` | `83f555893cc34ff6a8e5701e1a722b751aa0b3eeab362e2736d0f45b8484a6c4` |
| `Proofs/MF03/Finite12.lean` | `3304258460f2bb9fbebb792cb42642c72566fd706facfae56bef5a5d5051fa2b` |
| `Proofs/MF03/Finite13.lean` | `6b2ab289fcf4ed57f72fb3707513338fa984bb6ac920d4968a7dc660b7dacd91` |
| `Proofs/MF03/Finite14.lean` | `b28d1ec6b0422559133253607384e195dc388c5d829625a86dfd83d28e6385bf` |
| `Proofs/MF03/Finite15.lean` | `1520e0c1454ddb999e334595549b5e12f41a2e1374c5cd1037ae361ef2974aea` |

Paths in the table are relative to `lean-statements/NLA/`.

No existing module, target statement, CI, or metadata will be changed. The
new theorem must pass LeanCert kernel trust checks without axioms beyond the
usual `[propext, Classical.choice, Quot.sound]`.
