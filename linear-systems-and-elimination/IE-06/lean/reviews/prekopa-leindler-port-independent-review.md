# Independent Prékopa–Leindler port review

Reviewer: independent mathematical-review agent. Verdict: approved for adoption under the preapproved exact contract. This is a targeted source-diff and theorem-contract review; author compilation and full-package audit remain separate evidence.

Source: hojonathanho/isoperimetric commit 29768f8beeaf17295cdf3853d37da35d7e2b0a5f, Apache-2.0. Reviewed hashes:

- Basic.lean: adopted `fddbd8cacaa10fe57f8ab5f40909918de742f2d96661acd0734b868b978a703a`, upstream `29a29704257aaa78d0fd5146c23e01ec88ff1ee6408275e0f306bb60fcd2dc65`.
- PrekopaLeindler.lean: adopted `e329437b82157a06bbf1e6e36b7f38e2a04371f37615220c012470fce09caf23`, upstream `8a9d39059ec365fa0c91e49b199b535c2f7c361298bc2cde16fed2ac46dbeb83`.

I compared both complete adopted files against the pinned upstream files. No mathematical theorem statement or helper contract changed. Basic differs only by attribution, namespace, LeanCert import/options, and audit instrumentation. PrekopaLeindler has those changes plus Set lemma renames, Measurable composition API renames, a changed generated tactic case name, a measure-preserving embedded-integral proof replacing the older equivalent map-integral proof, and an almost-everywhere restriction proof using ae_restrict_mem. The latter still establishes the same inequality for every t in (0,1); no hypothesis was discarded. These are API/proof repairs, not assumption changes.

The exact final theorem is for Borel measurable ENNReal-valued f,g,h on positive dimension d+1, 0<θ<1, and the pointwise premise f(x)^(1−θ)g(y)^θ≤h(x+y). Its factor is the reciprocal ENNReal ofReal of (1−θ)^((d+1)(1−θ)) θ^((d+1)θ). It has no hidden finiteness or boundedness assumption. The normalized and bounded one-dimensional hypotheses are explicitly removed by the rescaling/truncation theorems before dimensional induction. Nonempty-set conditions in the one-dimensional Brunn–Minkowski helper are essential and are retained. The layer-cake formula permits infinite values and integrates positive real levels. Dimension zero is outside this final theorem and must remain a separate application case.

At θ=1/2 the normalization is 2^(d+1), correctly corresponding to the use of x+y rather than midpoint. This is suitable for the proposed Gaussian shift application after an explicit dilation change of variables and symmetry argument; the adopted theorem itself does not yet prove that application. No custom axiom, sorry, native evaluator, unsafe extension or new elaborator appears in these two sources. Every local declaration has a kernel trust assertion and printed axiom check in the port.
