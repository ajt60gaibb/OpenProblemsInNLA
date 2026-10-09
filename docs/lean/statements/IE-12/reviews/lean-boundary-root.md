# IE-12 independent final Lean statement review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve. Statement authors are `/root/statement_design` and `/root/infra_audit`.

The shared Program is a fixed finite syntax over finite label/register/constant indices, with globally fixed real constants. Each running step interprets one actual scalar opcode; no arbitrary transition, solver, cost or input-answer callback is supplied. Integer indexing operations are separately charged and there is no real-to-natural or digit-extraction instruction.

InputMemory places every dense A entry, b entry and epsilon at the exact reviewed addresses, then zero elsewhere. The quotient/remainder in free input placement is not a program instruction. Every read/write is a scalar indexed operation. Operands are read from the old state before one destination is changed, including overlap cases.

Division by zero and negative square-root inputs enter the distinct failed state; failure and successful halt are absorbing. A successful halt is a charged instruction and returns an actual consecutive memory slice of the original dimension. Natural run recursion counts every instruction and output cannot succeed while running or failed.

StreamLaw is the actual product of independent countably infinite standard-normal and fair-Bernoulli product measures, with proved probability-measure instances. The opcodes consume their separate next coordinates and increment only the corresponding cursor. There is no free access to the whole stream or an input-dependent law.

Target existentially chooses one P and positive real C,q before all n,A,b,epsilon. Every stream must give a bounded nonzero returned vector, including exceptional Gaussian draws. The same exact BoundedReturn predicate is used in the probability event with original A,b and the normwise A-only backward error. The target norm is the genuine Euclidean induced norm, so the norm-one/nonzero-output guards make its denominator positive.

The all-draw bound is C*n^2*epsilon^(-q), with real q, not expected runtime or q fixed to the stronger resolution. The probability comparison is exactly >=99/100, epsilon ranges over (0,1/2), and nonsingularity and arbitrary nonzero RHS are unchanged. No storage or conditioning premise is introduced.

Independently compiled the shared machine, live and frozen targets, eight operational controls and live=frozen identity using the pinned runtime/dependencies. All exited zero and reported only the three permitted standard axioms. Controls test actual addressing, charged halt, failure paths, absorption, sequential stream consumption and probability normalization. No solver-existence or runtime correctness theorem is asserted.

The full canonical snapshot, exact approved specification, shared machine and both target sources, dependency pins, implementation notes and independently generated local evidence are hash-bound. Linux CI remains separate; this review and identity certificate do not prove Target.
