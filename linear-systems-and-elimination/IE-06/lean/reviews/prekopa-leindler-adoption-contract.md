# Preimplementation contract for adopting Prékopa–Leindler source

Source: [hojonathanho/isoperimetric](https://github.com/hojonathanho/isoperimetric), commit 29768f8beeaf17295cdf3853d37da35d7e2b0a5f, Apache License 2.0. Upstream uses Lean v4.26.0-rc2. No upstream scripts or build hooks have been run; the repository was fetched only for source inspection.

The minimal source closure consists of Isoperimetric/Basic.lean (50 lines) and Isoperimetric/PrekopaLeindler.lean (786 lines). The full files were read. Their only external imports are Mathlib. Static searches found no sorry, admit, axiom, native_decide, unsafe, extern, implemented_by, custom elaborator or macro in these sources. Kernel compilation and transitive axiom audit remain required before adoption; static source inspection is not a trust certificate.

## Exact final contract to preserve

For every natural d, real theta with 0<theta<1, and Borel measurable ENNReal-valued functions f,g,h on Fin(d+1) to real, assume for all x,y that
$$
f(x)^{1-\theta}g(y)^\theta\le h(x+y).
$$
With the usual finite product Lebesgue measure, prove
$$
\operatorname{ofReal}\!\left((1-\theta)^{(d+1)(1-\theta)}
 \theta^{(d+1)\theta}\right)^{-1}
 \left(\int f\right)^{1-\theta}\left(\int g\right)^\theta
 \le\int h.
$$
All integrals here are nonnegative ENNReal integrals. Elaboration of the upstream Lean syntax places the inverse inside the real argument to ofReal; positivity identifies this with the displayed inverse of the ENNReal ofReal expression. The implementation bridge explicitly uses ENNReal.ofReal_inv_of_pos to pass between these equal forms. No boundedness or finiteness hypotheses occur in the final statement. The functions are evaluated at x+y, rather than a convex combination, which accounts for the dimension-dependent constant. Dimension zero must be handled separately in the eventual Gaussian application.

The proof first establishes one-dimensional Brunn–Minkowski for compact sets, extends by inner regularity to nonempty measurable sets, proves a layer-cake formula, proves the one-dimensional functional inequality for functions normalized to supremum one, rescales bounded functions, truncates to remove boundedness, and inducts on dimension by integrating the last coordinate. All helper contracts and normalizations will remain mathematically unchanged.

## Adaptation constraints

Only namespace/import changes, compatibility repairs for the pinned Lean 4.33.1/Mathlib API, explicit source attribution, and trust/axiom instrumentation are permitted. The original files and license will be retained byte-for-byte as source evidence. Dependency pins will not change. Any mathematical strengthening or changed hypothesis must be separately reviewed. Every adopted declaration must compile under the existing kernel and report only the foundational axioms, without an opaque additional assumption.

For Anderson's Gaussian shift theorem, theta=1/2 gives the factor 2^(d+1). Apply the theorem to f(x)=rho(x)1_K(x+u), g(y)=rho(y)1_K(y-u), and h(z)=rho(z/2)1_K(z/2). Convexity and the Gaussian midpoint density inequality give the pointwise premise. The right integral is 2^(d+1) gamma(K), and symmetry equates the two left integrals to gamma(K-u). Cancelling the positive finite scale gives the desired shift comparison. This application is still to be implemented and reviewed; adopting the external integration theorem alone does not claim completion of Anderson or IE-06.

## Port validation

The coordinator approved this exact contract before adaptation. The preserved-source port now compiles under the unchanged pinned Lean and Mathlib. All 27 declarations passed kernel trust assertions and foundational-only transitive axiom checks. The independent source review is recorded in prekopa-leindler-port-independent-review.md. Basic.lean has SHA-256 fddbd8cacaa10fe57f8ab5f40909918de742f2d96661acd0734b868b978a703a; PrekopaLeindler.lean has SHA-256 e329437b82157a06bbf1e6e36b7f38e2a04371f37615220c012470fce09caf23. Compatibility repairs changed restricted-measure AE proof syntax, the Fin 1 volume-preserving integral proof, and generated case tags; deprecated API names were updated. Every theorem statement is unchanged up to namespace.
