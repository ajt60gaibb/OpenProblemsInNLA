# SP-12 complete Lean source package

`Solution.lean` proves the unchanged full chromatic/SAP target as
`NLA.SP12.target`. For every positive order and every finite simple graph,
there is a real symmetric matrix with exactly its off-diagonal nonzero pattern,
a nonnegative quadratic form, the Strong Arnold property and nullity at least
the chromatic number minus one. The actual proper-coloring infimum, ordinary
matrix product, entrywise product and zero diagonal retain their reviewed
semantics. Isolated vertices, disconnected graphs and the singleton are included.

The self-contained source closure copies 36 SP-11 proof modules, 12 SP-12
proof modules and three statement/infrastructure modules byte for byte from
`lean-statements`; `proof-source-lock.json` records their imports and hashes.
The SP-11 prerequisites are identical to its actual Linux-accepted complete
proof. The SP-12 additions prove real LSS evaluation and predecessor independence,
Gram positivity and SAP, an actual Strong Delta realization, local surjectivity
of the nonedge Gram map, an actual one-vertex extension and the chromatic
induction. No external Hall theorem, analytic-surjectivity premise, continuous
choice, assumed graph realization or extra target hypothesis is imported.

The actual Gram derivative is surjective because any annihilating functional
would produce a forbidden symmetric SAP test matrix on the graph's nonedges.
The finite-dimensional inverse function theorem supplies nearby Gram factors
with the exact small cancelling nonedge entries. Injectivity of multiplication
on the fixed larger graph's test space is open and retains SAP. A nonzero small
coordinate gives exactly the new required edges. Deleting a low-degree vertex
preserves the chromatic number; restoring it increases both order and ambient
dimension by one. The actual Gram rank inequality completes the target.

The mathematical construction is credited to H. Tracy Hall,
[*The Delta Theorem*, arXiv:2601.01211v1](https://arxiv.org/html/2601.01211v1).
George Stepaniants authored the retained explanatory application note. Lean
implementation, packaging and independent reviews are AI-agent work; no
source-author participation or external human peer review is claimed.

Two independent preproof reviews approved the exact shared statement, and two
independent canonical boundary reviews approved the frozen Challenge before
Solution was written. The original statement, numerical specification, live
Lean statement and separate frozen Target retain their reviewed bytes.
`Identity.lean` proves their equality by `rfl`. `Challenge.lean` contains one
deliberate Comparator placeholder and imports only the statement; Solution
imports the actual proof and contains no admission. The old boundary lock and
preimplementation wording are retained as historical evidence; the final
complete source-copy lock is separate.

The full shared theorem passed local LeanCert kernel checks with only
`propext`, `Classical.choice` and `Quot.sound`. Independent source reviews and
fresh full-closure audits are retained under
[`docs/lean/proofs/SP-12`](../../../docs/lean/proofs/SP-12/README.md).
The [actual committed-project Linux receipt](../../../docs/lean/proofs/SP-12/LINUX_CI_RECEIPT.md)
records successful full-target Comparator/default-kernel acceptance, LeanCert
kernel trust and rejection controls at immutable commit
`529e7b0560cef6461c98e950046860a160e6f86c`, run `39142969327`.
Its independent artifact audit passes all 40 checks and every one of 96 original
project input hashes. The canonical page is now Lean verified. This descriptive
metadata refresh retains all 55 checked Lean inputs and will receive a fresh
committed-project CI check. Originals, IDs, paths and other canonical pages remain
preserved.

Pinned dependencies: Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. After materializing them:

```bash
lake build Challenge Identity Solution
```

At repository root, validate metadata and invoke the real Linux verifier:

```bash
python3 tools/lean/validate_manifest.py eigenvalues-and-inverse-problems/SP-12/lean
tools/lean/bootstrap.sh /absolute/outside/projects/nla-lean-tools
tools/lean/verify.sh eigenvalues-and-inverse-problems/SP-12/lean /absolute/outside/projects/nla-lean-tools
```

The verifier requires a committed unchanged self-contained package and the
normal unprivileged Linux isolation environment. It checks exactly
`NLA.SP12.target`, permits no replaceable definitions and allows only the three
foundational axioms. The SP-12 receipt above binds its actual immutable Linux-checked inputs; the
separate SP-11 receipt covers prerequisites. Do not commit dependency or compiled objects.
