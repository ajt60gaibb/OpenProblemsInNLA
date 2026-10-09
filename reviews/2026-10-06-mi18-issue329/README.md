# MI-18: review of issue #329

Date: 6 October 2026. Review coordinated by Codex, with separate statement and
verification-evidence agents. This is AI-agent review, not external human peer
review. The mathematical exposition was prepared by another Codex agent and
reviewed separately; it is not a manuscript submitted or approved by Kitamura.

**Decision: accept a complete negative resolution and promote MI-18 from
Partially resolved to Lean verified.** The catalog's [external-evidence
procedure](../../CONTRIBUTING.md#lean-verification) permits a reviewed public
Lean verification record. The source is linked at an immutable revision; the
external Lean repository and its dependencies are not vendored here.

## Sources and attribution

- [Issue #329](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/329), reported
  by **Kenta Kitamura** on 5 October 2026.
- [Pinned external proof](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b),
  commit `4200da4fc1a132d69c23fb877795b5b72089544b`.
- Catalog base `412489c6c52f49653bf069ac2f85e92034cdbfa5` (current published main
  when review began).
- [Author's dated build result](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build_results.json)
  and [full log](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/evidence/build.log).

Kitamura receives credit for the supplied certificate and formalization. The
external source discloses substantial AI assistance and makes no mathematical
discovery-priority claim. This review does not establish priority. Its
[license](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/LICENSE)
is Apache-2.0. Only the small ordered numerical certificate is reproduced with
the independently written exposition and Python verifier.

## Independent checks and their limits

1. The [statement audit](statement-audit.md) found an exact match of the complex
   field, fixed-order inversion statistic, interval, dimensions and hypotheses.
   Positive definiteness gives the PSD and positive-diagonal conditions. The
   unconditional `Bapat.exists_decreasing_pair` proves a strict decrease, not
   merely a failure of strict monotonicity. It therefore disproves the original
   arbitrary-order question.
2. The [evidence audit](evidence-audit.md) checked all 22 source hashes in the
   public manifest, the dependency pins, definition/target equality, proof
   import graph, and transitive axiom reports. The final declarations use only
   `propext`, `Classical.choice` and `Quot.sound`. The registration stub's
   intentional `sorry` is outside the complete proof's import graph.
3. The [independent certificate verifier](../../matrix-inequalities-and-norms/MI-18/verify_certificate.py)
   reconstructs the coefficient polynomials and their factorial-weighted norms
   using exact Gaussian-integer arithmetic from the 144 ordered rows. Its
   [recorded output](certificate-check.json) checks the strict endpoint sign.
   This is a computation of the finite certificate, not a new Lean kernel run.
4. The [mathematical manuscript](../../matrix-inequalities-and-norms/MI-18/solution.md)
   explains the permanent/coefficient identity, paired-minor derivative identity,
   ordered wedge polynomial, exact arithmetic and continuity argument. The
   [manuscript audit](manuscript-audit.md) records its separate review.

**No local Lean rerun was performed.** This computer had no Lean, Lake or Elan
installation. The reviewed author log, dated 5 October 2026 UTC, includes both
built and cached/replayed modules. It is not a fresh isolated catalog-side
rebuild or a catalog Comparator run. The two source/evidence reviews and the
independent integer computation are additional checks, not substitutes falsely
labelled as a local formal-verification run.

The result is existential in the positive perturbation and comparison points.
The particular numerical comparison for `10^70 H + I` mentioned in the external
README is not claimed here. Neither a smallest counterexample dimension nor a
real-symmetric counterexample is established. The published order-four result
and earlier rank-one/order-three results remain intact; they do not rescue the
universal assertion.

## Reproducing the external Lean checks

Use the exact commit and committed manifests. The main project pins Lean
`v4.33.1`, Formal Conjectures `89294ea02bd7cd678d59984add52cb4baef3dbf4`, and
mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The independent Lean4Web edition
pins Lean `v4.35.0-rc3` and mathlib
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. Other pins and exact audit-log hashes
are listed in [the evidence audit](evidence-audit.md).

With the pinned Lean versions available through Elan:

```bash
git clone https://github.com/KitaKen1/bapat-lal-q-permanent-lean.git
cd bapat-lal-q-permanent-lean
git checkout --detach 4200da4fc1a132d69c23fb877795b5b72089544b
cd lean
lake exe cache get
cd ../lean4web
lake exe cache get
cd ../lean
python3 scripts/build_audit.py
```

The script builds both editions, compares the registration statement with the
complete theorem, checks source restrictions and transitive axioms, and writes
`lean/evidence/build.log` and `lean/evidence/build_results.json`. Preserve the
original downloaded public record before rerunning: this script overwrites it.
Do not silently substitute newer dependency revisions. Retain the committed
manifest pins without running `lake update`.

When rerunning in an existing checkout, remove only the project build outputs
with `lake clean bapat_lal` from `lean/` and `lake clean bapat_lal_lean4web` from
`lean4web/`, then rerun the audit script from `lean/`. Naming the packages retains
the dependency build outputs; bare `lake clean` would also remove those outputs.
This optional rebuild is an additional reproduction step, not a claim about the
public run that was reviewed.

## Catalog and document validation

From the catalog root:

```bash
python3 matrix-inequalities-and-norms/MI-18/verify_certificate.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py MI-18
python3 tools/render_solutions.py MI-18
```

The [validation record](validation.md) records the actual results, document
inspection, and preservation checks. All existing IDs, registry mappings,
canonical paths and the original MI-18 mathematical question are preserved.
