# IE-22: complete proof sources, final verification pending

This self-contained package proves all 20 independently reviewed statements for the complete original IE-22 target: the genuine supremum over every real unit-row matrix has the canonical sharp constant, with the exact finite bound, an explicit uniform squared error rate, deterministic near-extremizers along every high-aspect sequence, the supremum limit, and optimality of the original eventual-uniform property.

Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial AI-agent assistance and all proof/review roles are disclosed in formalization.yaml. No contact email is added.

All project proof sources, including the 31 byte-identical vendored IE-21 modules, were freshly compiled locally. The 20 exact frozen theorem types and transitive closures passed with only propext, Classical.choice and Quot.sound. Final nonauthor whole-source reviews and authentic Linux LeanCert/Comparator verification remain pending. The canonical problem remains Solved until all required gates pass.

Definitions, Challenge, NUMERICAL_TARGETS.md and comparator.json retain exactly the bytes approved before implementation; reviews/statement-freeze.json binds them. Historical unreviewed-draft wording in those immutable records describes that earlier stage. Their 20 deliberate Challenge placeholders establish no mathematics; no proof imports Challenge. Solution explicitly selects authentic LeanCert kernel trust and checks every selected theorem. The independent statement and solution environments are compared by the pinned real Comparator.

IE-21 is reused from its verified immutable source commit 1eb284b84ecc0d3c958d022b3e020be7fa111391, now published as reviewed PR314 with full PR CI passing. reviews/IE21-DEPENDENCY.json binds all 31 source files. This package rebuilds them and uses no mutable local-path dependency, dependency axiom or imported compiled artifact.

Reproduce on the documented non-root Linux environment using the unchanged shared repository infrastructure: `tools/lean/verify.sh linear-systems-and-elimination/IE-22/lean TOOLS_DIRECTORY`. Default `lake build` compiles Solution; the full verifier additionally runs actual isolation/rejection controls, separate Comparator exports, permitted-axiom checks and default-kernel replay. Local cached development receipts are explicitly distinct from those authoritative gates.

The proofs use exact algebra, real analysis, finite-dimensional spectral theory and probability. The sharp Gaussian variance constant is proved through a one-dimensional crossing-kernel identity, absolutely continuous hinge fibers and finite-product tensorization. No floating-point integration, arbitrary truncation or numerical eigenvalue search is used. The exact schedule yields C=22+4L^2+8L for L=2/(1-theta).
