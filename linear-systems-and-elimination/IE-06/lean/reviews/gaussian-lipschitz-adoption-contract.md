# Gaussian Lipschitz concentration: proposed source-adoption contract

Proposed by `/root` for independent review before a compatibility port.
Source: https://github.com/YuanheZ/lean-stat-learning-theory,
commit d0f506f0a695018265dccb33bcb05e2f5ca1c876, Apache License 2.0,
upstream Lean 4.32.0. Source is downloaded read-only under /private/tmp; no
upstream build scripts or hooks have run. The transitive source closure of
SLT.GaussianLipConcen contains 27 files and 19099 lines. A static scan found no
sorry/admit/custom axiom/native_decide/unsafe/extern/implemented_by/elaborator/
macro declaration in that closure; this is not a substitute for kernel audit.

The final exact contracts to retain are as follows. On EuclideanSpace R (Fin n),
let gamma be the pushforward of the actual product N(0,1) law under the standard
coordinate equivalence. For n>0, L:NNReal with L>0, and LipschitzWith L f,

* f and exp(t*(f-integral f)) are integrable for every real t;
* cgf(f-integral f,gamma,t) ≤ t² L² / 2 for every real t;
* for every t>0, gamma{f-integral f≥t}.toReal ≤ exp(-t²/(2L²));
* the analogous absolute-deviation tail is ≤2 exp(-t²/(2L²)).

The Euclidean norm and actual Gaussian law must remain unchanged. Dimension
zero and zero Lipschitz constant are separate wrapper cases, not omitted from
later matrix applications. The chain uses proved Gaussian log-Sobolev estimates,
entropy tensorization, smoothing and limiting arguments; no log-Sobolev,
concentration, approximation, or integrability theorem may become a hypothesis
of these endpoints during porting.

Only exact source preservation with attribution, import relocation, pinned-API
compatibility repairs, and trust instrumentation are permitted. Minimal source
closure only; no dependency pin changes or upstream scripts. Original files,
license, manifest/toolchain and source hashes are retained. All adopted owned
declarations, including private helpers, must pass the transitive axiom audit.
The Gaussian coordinate measure must be bridged explicitly to the IE-06 law.

This is the Gaussian Lipschitz input for A1. The singular-value Lipschitz
functional and its expected value still require separate proofs; adoption of
this theorem alone does not prove the manuscript's spectral bound or IE-06.
