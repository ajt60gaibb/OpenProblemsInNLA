# TR-06: complete finite mean angular condition number

`Solution.lean` proves the unchanged intrinsic `NLA.Statements.TR06.Target` and
exports all ten exact published candidate declarations. The author build passes
all eleven LeanCert kernel assertions with only `propext`, `Classical.choice`
and `Quot.sound`. Canonical status is **Lean verified** after actual Linux run
40035041685 at exact proof commit `2b049df5` and two strict receipt replays.
All 45 controls and all 153 original package inputs passed. The descriptive
promotion changes receive a separate fresh Linux receipt; all 144 checked Lean
input bytes remain unchanged.

The law is induced Euclidean volume on the identifiable tensor locus, weighted
by the Gaussian of the tensor norm. The angular derivative individually
normalizes each recovered rank-one summand. The proof establishes actual
full-measure regularity and positive annular volume, bounds the whole normalized
graph by a finite controlled coordinate atlas and finite-type character fibers,
and derives angular and Gaussian integrability. No extra graph-volume or
integrability premise is assumed.

The package has 80 new proof modules, all 58 exact retained published sources,
the unchanged intrinsic statement and infrastructure, and four boundary modules:
144 Lean inputs in total. `proof-source-lock.json` and
[`sync-canonical-proof.py`](../../../docs/lean/proofs/TR-06/sync-canonical-proof.py)
check exact source copies and the explicit boundary/build inputs. Comparator
selects eleven theorem constants with no replaceable definition holes.
`Challenge.lean` holds eleven intentional specification placeholders and is
never imported by the proof. `Identity.lean` checks the literal target against
the independently reviewed statement.

Two independent canonical boundary approvals preceded Solution creation.
[Proof and verification records](../../../docs/lean/proofs/TR-06/README.md)
distinguish source reviews, fresh shared/canonical audits, author builds and
actual Linux acceptance. Metadata validation establishes consistency only;
the retained result for each audit records its scope, hashes and limitations.

With the pinned Lean 4.33.1 toolchain, reproduce the package build using
`lake build`. Run the repository's unchanged Linux harness for Comparator,
LeanCert proof trust and negative/isolation controls:

```sh
python3 tools/lean/validate_manifest.py tensor-computations/TR-06/lean
python3 docs/lean/proofs/TR-06/sync-canonical-proof.py
python3 tools/lean/harness.py bootstrap /tmp/nla-lean-tools
python3 tools/lean/harness.py verify tensor-computations/TR-06/lean /tmp/nla-lean-tools
```

The harness command is run from the repository root on its supported Linux
verification environment; its pinned setup and receipts are documented in
`docs/lean/README.md` and the CI workflow.

Original mathematical credit remains with Matthew J. Colbrook. Retained
formalization credit and license remain in every original source. New proofs,
packaging and independent reviews are AI-agent work. `ORIGINAL.md` preserves the
pre-promotion canonical page exactly; the original manuscript and problem files
are archived separately before any later status/render edits.
