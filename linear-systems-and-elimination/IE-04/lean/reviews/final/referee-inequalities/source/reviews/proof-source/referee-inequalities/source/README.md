# IE-04 Lean proof candidate

The package implements all 21 frozen obligations for the negative solution of
IE-04: a uniform exponential tail cannot hold for Gaussian-smoothed partial
pivoting. The mathematical solution and formalization are by George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. Substantial AI assistance is disclosed.

**Complete formal verification and publication acceptance are pending.** The
independent Definitions and all 21 Challenge statements passed actual Linux
elaboration after two independent statement approvals. Eight complete proof
modules passed development run 35029609317 with standard foundational axioms,
including the actual GEPP semantics, nonempty measurable rule class, exact
witness, Gaussian density/interval estimate and arbitrary-constant asymptotic
step. That complete build failed in Robustness and GaussianBox. Their candidate
elaboration repairs and the downstream probability/final modules require the
next actual run. No complete problem count is claimed from partial checks.

The proofs retain actual GEPP, its finite-product Gaussian input law, every
positive real pair of proposed tail constants, and all measurable admissible
tie rules. The witness box is proved nonsingular, so behavior on singular
inputs cannot manufacture the counterexample. Exact scalar error bounds and
symbolic induction cover the whole perturbation box. The only numerical
certificate is the fixed inequality exp(-2)>1/8, already accepted by LeanCert
in kernel mode; monotonicity and finite product measures provide the general
probability bound without high-dimensional interval subdivision.

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) fixes quantitative statements before
proofs. [SourceCorrespondence.md](SourceCorrespondence.md) maps the complete
original target and the prior IE-05 generic GEPP source to these proofs.
[comparator.json](comparator.json) requests all 21 exact independent targets;
[formalization.yaml](formalization.yaml) records current scope and verification
limits. Challenge is not imported into the proof graph.

The statement/proof separation follows Schiffer and Forsythe. One independent
complete mathematical source review has approved the proof route; two final
non-implementing source/evidence reviews, the complete source-matched Linux
build, and actual canonical Comparator/default-kernel replay with rejection
controls are required before a verified submission. These AI-agent reviews
apply scoped Tau Ceti standards; no official certification, external human peer
review or validation of the compiler/checker software is claimed.
