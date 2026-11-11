# TR-26 proof and verification evidence

The formalization proves the reduced nonisotropic degree $`6(d-1)`$ and the reduced isotropic degree $`2d`$ for every $`d\ge2`$. It uses the fixed unweighted embedding and bilinear form, with the full incidence ideal, both projective charts, and matrix-kernel directions.

The project is copied byte for byte from the independently reviewed
campaign revision `01141f415715a27473cabc1f35ef898e86aafae2`. Each of its 857 inputs matches
the SHA-256 map in the isolated Linux receipt. That run checked synthetic
merge `75c744ca3e500de926ddd77367594238b86728d4` and accepted these exports.

- `NLA.Proofs.TR26.nonisotropic_degree`
- `NLA.Proofs.TR26.isotropic_degree`
- `NLA.Proofs.TR26.target`

The run compared the frozen Challenge with the separate Solution and
accepted the exported proofs in Lean's default kernel. The LeanCert
audit checked theorem kinds, kernel trust, and the standard axiom set
`propext`, `Classical.choice`, and `Quot.sound`. The sandbox and
rejection logs record the harness controls. Mathematical source credit
belongs to Matthew J. Colbrook. The formalization and independent
reviews are credited in the project manifest and archived records.
[Archived source and package reviews](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/01141f415715a27473cabc1f35ef898e86aafae2/docs/lean/proofs/TR-26/FULL_TARGET_PACKAGE.md)
· [Independent artifact audit](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/01141f415715a27473cabc1f35ef898e86aafae2/docs/lean/proofs/TR-26/campaign-2026-10-26/linux-full-final-240e/inventory-independent/INVENTORY_REVIEW.md)
· [Original isolated Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40400589674).

The [retained receipt](previous-linux/result.json), [Comparator log](previous-linux/comparator.log),
and [LeanCert trust and axiom log](previous-linux/leancert-proof-trust.log)
are exact copies from that run. The project uses Lean 4.33.1 and pinned
Mathlib and LeanCert revisions. See the [immutable proof package](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/01141f415715a27473cabc1f35ef898e86aafae2/tensor-computations/TR-26/lean)
and its Lake manifest.

To reproduce the isolated run, prepare an unprivileged Ubuntu environment
with a user systemd session and Bubblewrap as in the
[repository workflow](../../../../../.github/workflows/lean-verification.yml).
Run the pinned harness from the repository root.

```sh
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh tensor-computations/TR-26/lean /tmp/nla-lean-tools
```
