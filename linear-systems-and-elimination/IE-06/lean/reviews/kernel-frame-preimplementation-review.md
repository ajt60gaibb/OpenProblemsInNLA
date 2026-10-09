# Fixed nullspace frame: preimplementation review

The full exact B4 contract, approved independently by root and this reviewer,
requires a fixed orthonormal nullspace frame. The source-statement author
requested this bounded implementation before its spectral/probability assembly.
For every actual M:Matrix(Fin m)(Fin(m+s)) Real with euclideanMap M surjective,
prove existence of Q:Matrix(Fin(m+s))(Fin s) Real satisfying Q^T Q=I and
range(euclideanMap Q)=ker(euclideanMap M). Rank-nullity gives kernel dimension
s, and an orthonormal basis of that finite-dimensional subspace supplies the
literal columns. This covers s=0 and m=0. There is no measurable dependence
on M asserted, and no new stochastic premise or axiom. The frame is chosen
inside each fixed-matrix fiber and eliminated from the intrinsic final event.

Completed implementation: `NLA/IE06/KernelFrame.lean`, SHA-256
`75368ae4d5461a75c9bbc35e7abdff36410edf1b94eff5bcd6c76ffdd3f5ee79`. All 1 local declarations passed their individual LeanCert
kernel-policy assertions and printed only foundational axioms (propext,
Classical.choice, Quot.sound), with no warnings. The pinned-runtime local-cache
receipt/log are in the corresponding review subdirectory. This does not claim
a fresh dependency rebuild or cached-dependency kernel replay. The coordinator
will independently review the frozen source.
