# SP-12 stable representation, SAP and chromatic gates — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of the eight SP-12 modules below. **Verdict: approve these
source bytes as the stated support gates.** The full frozen SP-12 Target is
not yet proved by this checkpoint.

| Module | Reviewed SHA-256 |
| --- | --- |
| `SAPTestSpace` | `175ab79714c2768de77fa195443c9ab6b084b95800772341f7d20b7e00c7d1c8` |
| `ExtendedRows` | `1294004dbc23d569595207243c4a941c057a5156db4c703a44ea589b23938e2c` |
| `RealLSS` | `94acc7cb479e5fe8411f08d4e2e19d9e434067c2eb6d8c37b2a60bcdf7a97b76` |
| `GramSAP` | `59f7f69833a7b1ab761ca19c2deaae008bb71ff32af2b69037c3dc26add36b5e` |
| `StrongDelta` | `6f96cf2f68bc640d251d9619ff2eec690fd1f59193951fa2f5080b20802d7fb2` |
| `Chromatic` | `cc992179d448fec2c5e892757b202669916b928f42e3525d49fce801f0af7ec1` |
| `Critical` | `bb8c43123d415a5b880ad6e788bff557c63ecf8856fbdd43d3df2a94b7ab79cf` |
| `ChromaticInduction` | `bc915b02d8a850c9a2e0eb8850376e766e79941f53d277154968ac04e204a9dc` |

`SAPTestSpace` uses exactly symmetric, zero-diagonal matrices vanishing on
graph edges. Left multiplication on this actual finite-dimensional subspace
is a continuous linear operator, and its injectivity is open in the multiplying
matrix. The equivalence to the original SAP explicitly requires exact graph
pattern: nonedges make the Hadamard constraint automatic, while nonzero edge
entries force the corresponding test entries to vanish. No changing
pattern-dependent domain is hidden in the openness statement.

`ExtendedRows` defines the actual new unit row and old rows with added first
coordinates. Its four Gram identities give the exact block formula. At zero
added coordinates the larger fixed test-space multiplication is injective:
the new unit block kills the first test row, symmetry kills its column, and
old SAP kills the remaining old test submatrix. This remains valid before
the new graph's incident edges become nonzero; it does not claim the base
matrix already has the full larger pattern. Continuity is proved for the
literal row/coordinate construction, including zero-dimensional cases.

`RealLSS` proves that evaluation of determinant-minor tensors and contraction
commutes with the actual shared-variable recursion. A dependent family of
earlier-nonneighbor inputs annihilates the alternating contraction, so a
nonzero output forces exactly that local input independence. No global
general-position or occurrence-specific variable assumption is introduced.

`GramSAP` proves PSD in the frozen double-sum formulation and equality of the
Gram kernel with the row-factor transpose kernel. For a nonzero SAP test
matrix, its maximal nonzero column has support only on earlier nonneighbors:
later entries vanish by symmetry/maximality, the diagonal vanishes, and edges
vanish by exact pattern plus the Hadamard equation. Its factor-kernel linear
relation contradicts the proved local input independence. The permutation
lemmas transport the full SAP with all three constraints.

`StrongDelta` specializes the actual completed SP-11 polynomial construction
at one faithful real assignment. Its nonzero outputs provide the local
independence needed for SAP. The same actual greedy permutation transports
pattern, SAP and degree/dimension bounds back. Its resulting Gram witness is
PSD by the preceding general Gram theorem. The empty auxiliary graph has a
separate literal empty witness. Thus Strong Delta is constructed here, rather
than assumed as a mathematical source axiom; the chromatic target still needs
the extension step.

`Chromatic` works with the frozen least-natural proper-coloring definition.
An order-coloring proves nonemptiness and attainment; nonempty vertex types
exclude zero colors. If the deleted vertex has fewer neighbors than available
colors, an actual unused color extends the old coloring. Degree below chi-1
therefore implies deletion preserves the exact chromatic number. Natural
subtraction and empty/singleton cases are handled explicitly.

`Critical` constructs the actual deletion embedding and proves its range is
all vertices except the chosen vertex. Relabeling and deletion preserve the
needed color/degree facts. It proves the critical minimum-degree bound and
constructs an actual induced embedded core of the same chromatic number with
sufficient minimum degree; no critical-core oracle is supplied.

`ChromaticInduction` maintains the exact dimension inequality for an actual
SAP Gram factor. When minimum degree already dominates chi-1, Strong Delta
suffices. Otherwise a chromatic-preserving deletion supplies the induction
witness and the explicitly quantified vertex-extension construction adds one
to both graph order and ambient dimension. The final conditional reduction
uses Gram positivity and rank ≤ ambient dimension to give the literal frozen
Target. Its extension premise remains visible; this review does not claim it
has been discharged.

Fresh immutable-source verification passed **48 Lean commands**: the eight
new SP-12 proof modules, 36 unchanged SP-11 proof modules, three statement/
infrastructure modules and a separate consumer. It audits **347 explicit named
declarations**, including **247 theorem/lemma constants**. The SP-12 contribution
is 58 declarations, including 48 theorem/lemma constants. Every proof name must
be Lean's theorem kind; every declaration passes `#assert_trust kernel` and
transitive `#print axioms`. Only accepted foundational axioms occur. All frozen
sources stayed unchanged; all ten dependency pins/tracked sources passed
before and after.

The **38 SP-11 prerequisite sources** additionally match byte for byte the
canonical inputs accepted by the real complete-SP11 Linux run at immutable
commit `9264361fafb89b37b5c48236afebb304bc84110a`. Their identity records are in
`verification/SP11-prerequisite-identity.json`. I implemented five historical
SP-11 supports; their independent source reviews come from other agents.
This report gives those unchanged prerequisites fresh runtime and exact-copy
evidence, not independent self-review.

```bash
python3 docs/lean/proofs/SP-12/verification/check-support.py
python3 docs/lean/proofs/SP-12/verification/check-SP11-prerequisites.py
```

Exact source snapshots, generated consumer, compiler/driver identities,
dependency checks and raw logs are in `verification/support-review/`. Project
objects are fresh and private; cached pinned dependencies are reused. This
is local macOS LeanCert kernel evidence, not an SP-12 Linux Comparator receipt
or full Target proof. `GramDifferential` and `VertexExtension` were excluded
from this frozen checkpoint because they were still under development.
No proof or canonical source was modified for this review.
