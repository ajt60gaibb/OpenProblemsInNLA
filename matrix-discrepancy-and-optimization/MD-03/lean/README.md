# MD-03 Lean proof

`NLA.MD03.target` proves the complete existing MD-03 statement with the
dimension-independent constant **36**. [Proof.lean](NLA/MD03/Proof.lean) translates
Gabriel Dahia's Komlós theorem from matrix discrepancy to explicit signs and
absolute row sums. It does not claim the sharper constant in the existing
Guo–Fang–Lu application note.

The [statement](NLA/Statements/MD03.lean), [frozen statement](Reviewed/MD03.lean)
and statement-checking infrastructure are byte-for-byte copies of the reviewed
files in `lean-statements/` at upstream commit
`775bedc1e33cc0951d08610cc7ba50d2901eda1a`.
[Identity.lean](Identity.lean) also checks equality of the two propositions by
`rfl`. The statement imports no Komlós definitions or proofs. LeanCert checks
statement/proof trust; no numerical certificate is used here.

## Dependencies and attribution

- Lean **4.33.1**, matching the repository's verification toolchain.
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- [Gabriel Dahia's Komlós library](https://github.com/gdahia/Komlos/tree/fac7d8f71f08caac7f5fe67786abe387cfe18b10),
  `fac7d8f71f08caac7f5fe67786abe387cfe18b10`, Apache-2.0.

All transitive revisions are fixed in `lake-manifest.json`. The root Mathlib pin
overrides the external package's original 4.34.0 dependency. This original
published library revision builds on 4.33.1 without source changes; the later
`d802857` refactor uses the newer `Finset.prod_le_one₀` name. Only `Komlos.Main`
and its dependencies are imported. The external `Challenge` and `Solution`
modules are never imported.

Dahia's formalization follows Sankeerth Rao Karingula and Shachar Lovett's
*An elementary proof of the Komlós conjecture* (ECCC TR26-188). The existing
catalog resolution credits Shengtao Guo, Ethan X. Fang and Junwei Lu, with an
application note by George Stepaniants (Department of Computing and
Mathematical Sciences, California Institute of Technology). Those historical
credits remain unchanged. The new bridge was implemented with OpenAI Codex
under Arav Bhattacharyya's direction; no source-author endorsement is claimed.

## Reproduction

Run from this directory:

```sh
lake exe cache get
lake build Solution Challenge Identity
python3 verification/check_sources.py
lake env lean NLA/MD03/Proof.lean
```

`Challenge.lean` intentionally contains one specification placeholder. The
solution does not import it and has no placeholders. The final command checks
kernel trust and prints the complete target theorem's transitive axioms.

## Verification boundary

See [verification/README.md](verification/README.md) for the retained local
build and axiom evidence. Existing independent reviews apply to the unchanged
statement files; new proof review and authoritative isolated Linux Comparator
verification are still pending. The catalog status is unchanged.

The MD-04 project uses a byte-identical copy of the small MD-03 bridge and the
same external dependency, keeping both projects self-contained for the fresh
project verification harness. Its substantive new argument is
`NLA.MD04.of_komlos`, which derives the reviewed MD-04 proposition from the
reviewed MD-03 proposition with the same constant.
