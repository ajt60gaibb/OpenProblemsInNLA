# IE-12 independent preimplementation review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve.

The exact original domain n>=1, nonsingular real A of Euclidean norm one, b nonzero and 0<epsilon<1/2 is retained. One finite program and positive real C,q precede every input and draw. The runtime is bounded on all draws, with nonzero output, while the original A-only backward error has probability at least 99/100. No conditioning, forward-error, storage or success-parameter strengthening is introduced.

The finite syntax exposes every scalar arithmetic/square-root/comparison/random draw and charges scalar memory, branch and address operations. Unbounded indexed storage is concrete, with dense input and zero elsewhere, not an input-answer oracle. Integer counters have charged natural arithmetic and only a natural-to-real conversion; there is no real-to-integer, floor, logarithm, digit extraction or black-box solve.

Fixed finite real constants are uniform program data. Gaussian and bit streams are independent concrete product laws and consumed sequentially, including adaptive selection of instruction types. Explicit initialization, finite successors, absorbing successful/failure tags and bounded natural iteration determine the output rather than a supplied evaluator or cost.

The original permitted exact-real model and archived manuscript expressly allow unit-cost indexed scalar-array reads/writes with charged integer loops. I inspected its problem/result, table-access and all-realizations sections. Every-draw termination includes zero Gaussian events and nonzero fallbacks, and no dimension-dependent logarithm is hidden in the fixed C. The q=3 stronger result is retained as source context only.

The model must be implemented and independently reviewed, including actual countable product measures and scalar transition semantics. Neither the target nor source-algorithm correctness is assumed by this specification. Exact source and full original snapshot are preserved.

Scope: exact specification review before Lean implementation; no Target proof or later compiled model is certified.
