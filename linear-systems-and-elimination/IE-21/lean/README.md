# IE-21: complete proof sources, final verification pending

This package implements all 23 independently reviewed statements for the full canonical IE-21 target, including exact quantitative bounds and convergence for every sequence with n→∞ and m/n→∞ on arbitrary changing probability spaces. Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology.

All proof modules compile locally and their selected transitive axiom closures use only `propext`, `Classical.choice`, and `Quot.sound`. Fresh final nonauthor reviews and authenticated Linux LeanCert/Comparator verification are still pending. The canonical problem remains Solved until those gates pass.

The unchanged `NUMERICAL_TARGETS.md`, Definitions, Challenge and Comparator configuration are the exact boundary frozen after two independent preproof approvals. Their historical draft wording records that stage; `reviews/statement-freeze.json` binds their bytes. The 23 deliberate Challenge placeholders are specifications only. No proof module imports Challenge. The final Solution imports the authentic LeanCert verifier, explicitly selects kernel trust and checks every selected theorem.

Reproduce through the shared repository infrastructure: `tools/lean/verify.sh linear-systems-and-elimination/IE-21/lean TOOLS_DIRECTORY` on the documented non-root Linux environment. The default `lake build` compiles Solution, while the full verifier additionally runs real controls, isolated Comparator exports, permitted-axiom checks and kernel replay. Local cached development checks are documented separately in `reviews/` and are not a substitute for that full run.

The proofs use exact analytic identities, finite geometric and probabilistic bounds, and limiting arguments. No floating-point approximation or numerical integration is needed. LeanCert is used through its authentic kernel-trust assertions.
