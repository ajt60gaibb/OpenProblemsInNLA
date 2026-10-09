# Reviewed Lean statement boundaries

This package records propositions for the original permanent problem targets.
A declaration `def Target : Prop := ...` states a question; it does not prove
the proposition or change the problem's mathematical status. Existing
`category/ID/lean/` proof projects and their verification gates are unchanged.

Lean is pinned to 4.33.1, LeanCert to
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. The committed Lake manifest pins
every transitive package. The only deliberate placeholders live in the trusted
Comparator challenge and rejection controls; problem definitions contain none.

For each permanent ID, retain the complete canonical README as
`docs/lean/statements/ID/ORIGINAL.md`, byte for byte. Write
`NUMERICAL_TARGETS.md` in the same directory with the complete domains,
quantifiers, dimensions, fields, norms, constants, strictness, endpoint and
degeneracy conventions, probability laws, algorithm/cost model where relevant,
and every original subquestion. Record any ambiguity rather than silently
strengthening or weakening the target. Obtain two independent specification
reviews before implementing `NLA/Statements/IDWITHOUTDASH.lean`.

Use exactly one namespace `NLA.Statements.IDWITHOUTDASH` with the matching
`end`, a closed `def Target : Prop`, and one plain `import` per line. The target
may refer to explicit local mathematical definitions and pinned library APIs.
Free proposition parameters standing in for unstated mathematics, invented
algorithm guarantees, and opaque predicates that merely rename prose are not
complete formalizations. Independent reviewers must inspect imported meaning.

Freeze the Lean boundary before its final independent reviews:

```bash
python3 tools/lean_statements/check.py freeze MD-03
```

This retains a separate `Reviewed/MD03.lean` namespace. It refuses to overwrite
an existing snapshot. A deliberate mathematical revision requires a new
specification and two new independent boundary approvals. Never refresh frozen
inputs in CI. Two reviewers distinct from all authors must approve both the
specification phase and the final Lean boundary phase; the same independent
pair may perform both phases. These are disclosed AI-agent reviews, not human
peer review. The order is recorded by the reports and work history; hashes
alone cannot prove chronological ordering or mathematical fidelity.

Metadata at `docs/lean/statements/ID/statement.json` has this shape:

```json
{
  "schema_version": 1,
  "id": "MD-03",
  "scope": "statement-only",
  "canonical_readme": "canonical/category/MD-03/README.md",
  "source_sha256": "64 lowercase hex digits",
  "specification": "docs/lean/statements/MD-03/NUMERICAL_TARGETS.md",
  "specification_sha256": "64 lowercase hex digits",
  "module": "NLA.Statements.MD03",
  "declaration": "NLA.Statements.MD03.Target",
  "lean_sha256": "64 lowercase hex digits",
  "frozen_sha256": "64 lowercase hex digits",
  "authors": ["implementing agent identity"],
  "reviews": [{
    "reviewer": "independent agent identity",
    "is_ai": true,
    "phase": "specification",
    "verdict": "approve",
    "report_path": "docs/lean/statements/MD-03/reviews/report.md",
    "report_sha256": "64 lowercase hex digits",
    "input_sha256": {"repository/relative/path": "64 lowercase hex digits"}
  }]
}
```

Each specification review binds the canonical README, `ORIGINAL.md` and
`NUMERICAL_TARGETS.md`. Each `lean-boundary` review also binds the live and
frozen Lean files, their complete local import closures, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`. `review_inputs` in the checker
enumerates the required paths. All reports themselves are hash-bound. The
validator rejects mismatched hashes, missing reviews, author self-review,
unregistered paths, symlinks, unregistered Lean modules and missing snapshots.
The published-base check prevents deletion of an entire statement record.

After adding metadata, generate the separately checked identity certificates:

```bash
python3 tools/lean_statements/check.py refresh-identities
python3 tools/lean_statements/check.py --base-ref origin/main validate
python3 -m unittest discover -s tools/lean_statements -p 'test_*.py' -v
cd lean-statements
lake exe cache get
cd ..
python3 tools/lean_statements/check.py elaborate --output /tmp/nla-statement-evidence
```

The development-only `--draft` flag omits approval-count checks. It must never
appear in CI or be described as reviewed verification. A receipt labels that
scope explicitly. The elaborator checks that every target is a safe definition
of closed type `Prop` and its entire axiom closure contains only `propext`,
`Classical.choice` and `Quot.sound`. It also checks definitional identity of
each current proposition with the separate frozen proposition.

`StatementControls.lean` has executable rejection controls for target axioms,
wrong types, free parameters, custom axioms, `sorryAx`, and actual
`native_decide` trust. `KernelSmoke.lean` proves only the infrastructure bound
`Real.log 2 < 7/10` using explicit `leancert (trust := kernel)` with the global
kernel option and `#assert_trust kernel`. This small certificate demonstrates
the numerical route; it is unrelated to any catalog solution. Pure proposition
definitions require no artificial interval computation.

On credential-free non-root Linux, the existing unchanged harness checks the
identity certificates and smoke certificate in fresh real isolation:

```bash
tools/lean/bootstrap.sh /tmp/nla-statement-tools
tools/lean/verify.sh lean-statements /tmp/nla-statement-tools
```

That harness requires the package to be committed and unchanged. The generated
Comparator configuration lists `Target = ReviewedTarget` certificates and the
infrastructure bound, with no definition holes and only the standard axioms.
It does **not** list or prove `Target`. Equality of two statements establishes
neither one's truth. Local macOS elaboration is not authoritative Linux
Comparator evidence. Successful frozen-boundary comparison also cannot replace
informal-to-formal mathematical review; shared imported definitions remain
trusted, pinned and review-bound inputs.

The separate `lean-statements.yml` workflow validates reviews, runs declaration
rejection controls and LeanCert kernel checks, then invokes the existing Linux
Comparator harness. It never promotes a catalog status or relaxes proof gates.
