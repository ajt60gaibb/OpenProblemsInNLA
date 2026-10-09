# FR-05 independent exact-statement review

**Verdict: APPROVE for source fidelity of the existing Lean theorem statements.** Reviewer: `/root/fr05_review`, 2026-10-09. This does not assert a new proof, complete transitive proof audit, or isolated Linux Comparator result. FR-05 already had a Lean statement before the present statement-generation task; no replacement target or permanent ID is introduced.

The canonical README asks whether `p_d → 0` for every `d≥2`, where `p_d` is the probability that an iid standard complex-Gaussian `(4d−5)×d` frame has the **all-signals** phase-retrieval property under componentwise absolute values and a single global complex phase. Its resolution cites Li's stronger exact bound `p_d ≤ C/d` for one absolute `C>0` and every `d≥2`. The local `NUMERICAL_TARGETS.md` records the same bound and original limit, without selecting an unsupported numerical value for `C`.

`Definitions.lean` uses actual matrix rows, complex-linear measurements, norm equality in each row, universal quantification over `x,y`, and `exp(θ i)` with `θ:ℝ` for the global phase. `Probability.lean` maps a real standard Gaussian on every real and imaginary entry coordinate through the factor `1/√2`, giving the required independent `N(0,1/2)` coordinates. Its event has exactly `4*d−5` rows and its real `phaseRetrievalProbability` is the event probability. `InjectivityMeasurable.lean` proves the event measurable. For `d≥2` the natural subtraction is the intended integer row count.

`Solution.lean` exports both `∃ C:ℝ, 0<C ∧ ∀ d≥2, p_d≤C/d` and `Filter.Tendsto p Filter.atTop (𝓝 0)`, so its theorem *statements* include the complete original target and the cited stronger quantitative conclusion. Its `Challenge.lean` mirror has intentional `sorry` placeholders and is not imported by `Solution.lean`; those placeholders do not weaken the exported theorem statement. The canonical README itself leaves an independent proof review and isolated Linux Comparator/kernel verification outstanding, and this review does not change that status.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-05/README.md` | `fcf01b335bccd51d025c1184a4b668f52431af9209cf5d88dcb7e95345507554` |
| `frames-and-matrix-designs/FR-05/lean/NUMERICAL_TARGETS.md` | `c8a869a17f5eb85621a78a9de14ffc23a55c0d8ca183230311b17b877532f2c4` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Definitions.lean` | `aaf435d209909c7d08114dcc2cfda9595408c5aa5a85537b0972032c0357a78e` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Probability.lean` | `0aacb415bf3e8dd33359f6e8f25f52ea950c9b3e7014227f051c8bc11ee093c5` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Geometry/InjectivityMeasurable.lean` | `417cb019d234d86f40e43594691e5d897333b75ae886b3e5089620b9619618bc` |
| `frames-and-matrix-designs/FR-05/lean/Solution.lean` | `7bdf86cd414a560f9bb470ef0bda254c1b7a4517922f00032d0ca9e78c7feec4` |
| `frames-and-matrix-designs/FR-05/lean/Challenge.lean` | `f92211491c88a6661f06f2ee64f596722f0f473481a915e1a429285bb927c776` |
| `frames-and-matrix-designs/FR-05/lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
