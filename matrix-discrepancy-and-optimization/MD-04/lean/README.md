# MD-04 Lean proof

`NLA.MD04.target` proves the complete existing Beck–Fiala target, with constant
**36**. [Reduction.lean](NLA/MD04/Reduction.lean) proves the implication
`NLA.Statements.MD03.Target → NLA.Statements.MD04.Target` using only mathlib and
the reviewed statements. [Proof.lean](NLA/MD04/Proof.lean) supplies the proved
MD-03 theorem.

For a 0–1 matrix, column sums equal sums of squared entries. Dividing by
`Real.sqrt t` therefore gives the unit column bound required by MD-03. Since
`t ≥ 1`, the square root is positive; multiplying the signed row bound back
gives `C * Real.sqrt t`. The same constant works for every permitted dimension
and sparsity, and every column receives a sign.

## Unchanged statements and shared proof

Both [MD-03](NLA/Statements/MD03.lean) and [MD-04](NLA/Statements/MD04.lean),
their `Reviewed/` copies, and the statement-checking infrastructure are copied
byte for byte from `lean-statements/` at upstream commit
`775bedc1e33cc0951d08610cc7ba50d2901eda1a`.
[Identity.lean](Identity.lean) checks both frozen equalities by `rfl`.
Neither proposition imports the Komlós library. LeanCert supplies trust checks;
there is no numerical certificate in this proof.

The 35-line [MD-03 bridge](NLA/MD03/Proof.lean) is copied byte for byte from the
MD-03 project so this project can be verified from a standalone snapshot.
Both projects use the same pinned external proof, without copying its source.
`verification/check_sources.py` checks these source correspondences when run
inside the repository and verifies the dependency and source pins.

## Dependencies and attribution

Lean **4.33.1**; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`;
LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`;
[Gabriel Dahia's Komlós library](https://github.com/gdahia/Komlos/tree/fac7d8f71f08caac7f5fe67786abe387cfe18b10)
at `fac7d8f71f08caac7f5fe67786abe387cfe18b10` (Apache-2.0).
The root Mathlib pin overrides the library's original 4.34.0 dependency; the
selected library source compiles unchanged. All transitive pins are retained
in `lake-manifest.json`.

The substantive proof is Dahia's formalization of Karingula–Lovett's Komlós
argument. The catalog's existing Guo–Fang–Lu resolution and George Stepaniants
application-note credit remain unchanged. The latter's affiliation is the
Department of Computing and Mathematical Sciences, California Institute of
Technology. This bridge and scaling proof were implemented with OpenAI Codex
under Arav Bhattacharyya's direction. No sharper constant, human review or
source-author endorsement is claimed.

## Reproduction and verification boundary

Run from this directory:

```sh
lake exe cache get
lake build Solution Challenge Identity
python3 verification/check_sources.py
lake env lean NLA/MD04/Proof.lean
```

The single deliberate placeholder in `Challenge.lean` is excluded from the
solution. The final command checks kernel trust and prints the target's
transitive axiom report. See [verification/README.md](verification/README.md)
for local evidence. The unchanged statements retain their existing reviews;
independent review of the new proofs and authoritative isolated Linux
Comparator verification remain pending. The catalog status is unchanged.
