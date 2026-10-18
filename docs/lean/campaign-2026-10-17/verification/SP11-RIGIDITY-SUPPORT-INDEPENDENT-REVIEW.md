# SP-11 canonical and class-rigidity supports — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**Verdict: approve the seven source modules below at the listed hashes.**
I did not implement them. This review extends the preserved tree/color
checkpoint; it does not replace its evidence.

| Module | Reviewed SHA-256 |
| --- | --- |
| `CanonicalColoring` | `bc1e9ea1cccf8c9805f28c7b0a5062a3fa871c7a2d1e472b8d1609c57faf9830` |
| `CanonicalPair` | `c93349e3f15c83b6127686fd69ad68ce5525c317b7946852c03eebe49969d37c` |
| `CanonicalOutputs` | `bc30ca6bea86eb1100bc983f40ad0e6c9ebd35c9121ff943f0f774ade4d73151` |
| `ColorRigidity` | `0454ea402344587a986a46a9e11307bd8d7e409af0b5182047dfeaa66167bc41` |
| `DoubleOccurrenceShape` | `9298fbb70a4a78f04fd7e5541e91e3bc4de81895f416d64791ce27e651d37da4` |
| `OrdinaryBlockers` | `751ec7b20b1ffd73c89436311b9db7f2762acd92da45fbd7a18af55666c64b8d` |
| `GramCoefficient` | `9860b3c5ed250276225be71a779afc049ca5462ee00f37c97392bceded145a89` |

`CanonicalColoring` uses the actual sibling slot for each ordinary child
output. Its recursive admissibility proof needs the precise structural
inequality child arity ≤ sibling slot and the stated ambient dimension bound.
The inserted coloring skips one cap slot, which never decreases a child's
slot value; this preserves the same recursive argument. The actual LSS tree's
structure is derived from `OrderedGreedy`, rather than assumed from a drawing.

`CanonicalPair` joins the early normal coloring and the later inserted
coloring with one exactly shared cap. Its cap position counts the later
root's actual predecessors below the early label. The greedy insertion bound
establishes admissibility of the early root; the later root uses all distinct
cap/skip slots. The sign is therefore nonzero. This holds for ordered roots
including nonedges, so admissibility alone is correctly not presented as
noncancellation. The equal-root case uses the final insertion slot.
`CanonicalOutputs` gives the literal input values at every actual occurrence,
handling the later top root separately and retaining normal values below it.

`ColorRigidity` inducts on original vertex labels, not occurrence identities.
Earlier children have already recovered their canonical outputs, so equality
of incident totals in one label class cancels the child totals. Pointwise
canonical lower bounds and equality of class output sums force equality at
every occurrence. The second theorem derives those bounds from the explicit
earlier-label tie or smaller-color blocker condition. Repeated labels and
multiple occurrences within a class are retained throughout.

`DoubleOccurrenceShape` supplies the genuine paired child map, child conduit
identity, strict label inequality, and incident class equations from the
previous exact signed expansion. Its recovery theorem still requires the
displayed blocker/tie condition for every actual occurrence. It does not hide
this remaining graph-specific obligation inside a definition.

`OrdinaryBlockers` obtains each smaller canonical color from an earlier
ordered sibling. The specialized witnesses are actual child occurrences of
the actual parent, and their distinct actual outputs follow from the parent's
injective tuple. `GramCoefficient` then reads exactly the coefficient in
`polynomialGram` using the proved paired-garden expansion. Its uniqueness
hypothesis concerns nonzero-sign actual summands; zero-sign summands may
share the chosen exponent. Only its nonvanishing corollary additionally needs
a nonzero chosen sign. Both statements are mathematically exact.

The independent fresh-source audit passed **35 Lean commands**: 32 proof
modules in the local closure, two statement/infrastructure modules and one
consumer. It checks **263 explicit named declarations**, including **176
theorem/lemma constants**, using theorem-kind assertions, LeanCert
`#assert_trust kernel`, and transitive `#print axioms` output. The only axioms
are the accepted foundational ones. All ten dependency pins/tracked sources
passed before and after, and all frozen project source bytes remained equal.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py \
  --evidence-name sp11-rigidity-support-review \
  --top OrdinaryBlockers GramCoefficient ColorRigidity DoubleOccurrenceShape \
        CanonicalColoring CanonicalPair CanonicalOutputs PriorInsertion AugmentedColors
```

The exact source snapshots, generated consumer, compiler and driver hashes,
raw logs and machine-readable result are in `sp11-rigidity-support-review/`.
Source elaboration used fresh private output objects and pinned cached
dependencies. It excluded the campaign's existing project objects. Five
self-authored modules in the transitive closure have runtime evidence here;
their independent source reviews come from other agents.

This checkpoint excludes the later `DiagonalUniqueness`, `TopOccurrences`
and edge blocker work. It is local macOS LeanCert kernel-trust evidence,
not a Linux Comparator run, and does not prove the full frozen SP-11 `Target`.
