# TR-14 contextual product step and actual minimal ordinary witnesses — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these sources. **APPROVE the exact three requested sources and the reduced-subalgebra finiteness dependency below.** These are actual contextual and decomposition gates, not yet the full ordinary lower bound or Target.

| Module | SHA-256 |
| --- | --- |
| `ContextualProductStep` | `5d2928c68fa47ae093c40ba142fe5fada6f32e5ae6fea470c69a98abb4f706da` |
| `ContextualProduct` | `a29b46a097cf27117798fd11415f7af269aa84cdaaad6cd8010bfed341ed0ea2` |
| `MinimumOrdinary` | `3016510412bdbadc0415c375f2606aac09ac801d1d1ecb182a5ce9f77bb5c4b9` |
| `ReducedSubalgebras` | `8c5e789cd451446e05d02fd079b1fb9a0421c8029b2e98d3c9c82eafdd662683` |

`ContextualProductStep` applies the proved per-unit transformation to every actual unit in U. It proves each resulting auxiliary algebra reduced from the exact Frobenius/full-first-projection context, unit first component, actual T-stability and T*Q⊆W. Thus its finite classification is only over reduced algebras. Their actual unit classes cover all units in U; the proved finite-class unit-span theorem supplies one class spanning U. Its algebra then stabilizes U*V by linear-span and product-span induction. A member of the nonempty spanning class supplies the transformation dimension inequality, while actual inclusions bound its T and S dimensions by U*V and its stabilizer. The subsingleton ambient case is discharged before the nontriviality argument. No arbitrary-subalgebra finiteness or product inequality oracle is hidden.

`ReducedSubalgebras` establishes the remaining finiteness over the complex numbers. A reduced finite-dimensional commutative complex algebra is Artinian and decomposes into its actual maximal residue fields. Each residue field is a finite integral complex extension, so algebraic closedness makes its scalar map surjective. Pullbacks of coordinate indicators are idempotents spanning the algebra. A reduced subalgebra of a possibly nonreduced ambient algebra is therefore determined by its actual ambient idempotents. The Artinian ambient ring has finitely many idempotents via their genuine equivalence with clopen prime-spectrum subsets; its spectrum is finite. Injecting reduced subalgebras into subsets of that finite idempotent set proves the required finiteness. Reducedness is imposed only where mathematically needed, and ambient nilpotents are allowed.

`ContextualProduct` instantiates precisely that theorem to remove the finite-reduced-algebra premise over ℂ. Its actual Frobenius nondegeneracy, full projection of V*Q, functional annihilation of W, UVQ⊆W and one-membership conditions remain explicit. These must still be constructed for the later ordinary-decomposition graph/block application. This is an established contextual dimension inequality, not a completed application to every tensor.

`MinimumOrdinary` obtains a least actual ordinary width no larger than an existing supplied witness. Its coordinate functions are exactly the original mode-dependent rank-one products. A nonzero coefficient in a linear dependence solves one summand in terms of the others; the exact finite erase/reweight identity then removes that summand. The new weights are absorbed into mode zero using the explicit positive-order condition. Minimality therefore forces linear independence of the genuine tensor-coordinate functions, not only a flattening. Independence excludes an identically zero entire mode factor, while individual coordinates may remain zero. Width zero is handled separately; no Vandermonde, symmetry, general-position or coordinatewise-nonzero condition is introduced.

Independent immutable verification passed **16 Lean commands**, comprising 15 actual local sources plus a separate consumer, **57 explicit declarations**, and **53 theorem/lemma-kind checks**. Every explicit constant passes LeanCert kernel trust and printed transitive axiom checks; only propext, Classical.choice, Quot.sound occur. All source bytes and all ten dependency pins/tracked trees pass before/after. All local output objects are built in a fresh private directory; only pinned cached dependency objects are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-contextual-support.py \
  --top ContextualProduct MinimumOrdinary --evidence-name contextual-support-review-3
```

The exact driver, frozen sources, consumer, hashes and raw compiler output are in [verification/contextual-support-review-3/](verification/contextual-support-review-3/). Earlier product/reducedness/unit-span/transformation support reviews remain separately retained. No mathematical source, original statement, permanent ID or canonical page was edited. This is independent source review and local macOS Lean4.33.1 kernel evidence, not a full Target proof, Linux Comparator receipt, external human peer review or source-author endorsement.
