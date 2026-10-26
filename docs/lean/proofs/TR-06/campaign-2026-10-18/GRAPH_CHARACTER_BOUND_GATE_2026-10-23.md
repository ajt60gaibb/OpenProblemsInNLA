# TR-06: uniform bounds for actual normalized-graph characters

23 October 2026. Author: campaign recovery/algebra agent. This is an author scope report for two new support modules. It is not independent approval, a full TR-06 proof, Linux CI, or Comparator evidence.

The earlier 24 frozen algebra/radial sources were recovered byte for byte from the surviving author transcript. Their original hashes and authored reports were preserved; recovery did not turn old receipts into current execution claims. The formerly unfinished character-bound file was completed with the two ordinary elaboration fixes recorded below. None of the 24 frozen sources was edited.

| New source | SHA-256 |
| --- | --- |
| `GraphProjectionCharacterBound.lean` | `60a155829ea4c83cfd4d76c6a952c8e4aa8c7344a191e9b63e0151ea8cd4bfc5` |
| `GraphProjectionOrderedBound.lean` | `9cb27bec5644f321dfa890907c0179fc933edb9545e619aa7626eb5f3cada531` |

Both files are in `lean-statements/NLA/Proofs/TR06/`. Their source lock is `graph-character-bound-source-lock-2026-10-23.json`. All five exported declarations have passed LeanCert kernel assertions with only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact contracts

Namespace: `NLA.Proofs.TR06.GraphProjection`.

`exists_uniform_aeval_character_finset_bound f` works for an arbitrary commutative finite-type complex algebra S and finitely many genuine elements `f : Fin k → S`. It chooses one natural B before the projected value x. Every finite set q of genuine complex algebra characters has cardinality at most B if every character takes f to x and the actual polynomial-coordinate map `MvPolynomial.aeval f` is quasi-finite at its actual character kernel. No reducedness, integral-domain, supplied Noetherianity, global finiteness, or already finite whole fiber is assumed. Noetherianity of S is proved from finite type over the field ℂ.

`exists_uniform_aeval_character_family_bound` gives the corresponding bound for every explicitly finite index type and every injective indexed character family. This avoids using a finite-cardinality convention on infinite sets. `exists_uniform_row_character_family_bound` instantiates it with the genuine normalized-graph source algebra and the actual real row-coordinate polynomials. One B works for every real row value and every finite injective family of actual source characters at quasi-finite kernels.

`ambientValues_injective` proves that the literal input and normalized-output coordinates separate the genuine Hilbert graph ambient. `exists_uniform_ordered_graph_family_bound` then bounds every finite family of distinct actual ordered-pivot normalized graph points with fixed pivot pattern and row map, common projected value, nonzero actual amplitudes, and injective genuine projected Fréchet derivative at each point. The last premise is the exact geometric obligation discharged by the separate controlled projection atlas. It is not replaced by real setwise local injectivity.

## Proof and completed boundary

For each projected value, the proof equips ℂ with the actual base action obtained by evaluating the coordinate polynomial ring at that value. Character equality on the finitely many coordinate generators proves compatibility on every base polynomial. Each original complex character therefore lifts to a character over that actual base action. The lift is injective by pointwise equality, so the finite-set cardinality is unchanged. The retained, proved uniform quasi-finite character theorem then supplies one bound independent of the chosen target base action. The historical unfinished proof failed only at the pointwise lift-injectivity elaboration and the unfolding of its finite image before a cardinality rewrite; both are now proved directly.

For actual ordered graph points, equality of two characters forces equality on every genuine graph coordinate. The proved real-coordinate correspondence and injectivity of ℝ→ℂ imply equality of every actual input and normalized-output coordinate, hence equality of the actual graph points. Their assumed distinctness gives character-family injectivity. Actual projected derivative injectivity supplies genuine quasi-finiteness through the separately proved real/imaginary point-derivation and cotangent-fiber argument.

Extraneous complex source points and all radius branches remain in the source algebra. Counting a larger algebraic family is valid for the required upper bound; no identification of all algebraic characters with real graph points is asserted. The separate finite pivot union and controlled atlas must still turn these bounds into the actual complete graph's finite Hausdorff volume. This report does not claim the final intrinsic angular-mean theorem.

## Execution evidence

The two new files have compiled directly under exact Lean 4.33.1, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, with the pinned read-only Mathlib and LeanCert dependencies. Their five explicit kernel assertions pass. The separate immutable replay in `graph-character-bound-development-2026-10-23/replay.py` passed all 52 commands: 51 exact project sources plus a consumer that asserts kernel trust and prints axiom closure for all five new declarations. Its `result.json` binds every source and execution log hash. The runner uses fresh private project outputs and checks current source hashes against immutable snapshots before compilation. Historical receipts remain separate.
