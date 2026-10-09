# IE-12: exact mathematical and numerical specification

Permanent ID: IE-12. Canonical README: linear-systems-and-elimination/IE-12/README.md. Campaign base: 80c0e3e638b2f26dcb3a00353651fc3d2215dd65. Existing status: Solved. No Lean declaration exists in the canonical problem directory at this base.

## Review and verification boundary

Author: OpenAI Codex AI agent /root/statement_design, 2026-09-28. This is a preimplementation mathematical/model specification. It defines no Lean target and proves no catalog problem. Two independent approvals must bind the final specification before implementation. The complete original page, including resolution, attribution and historical statements, is preserved byte-for-byte as ORIGINAL.md. No canonical file, ID, path or status is changed.

The eventual statement must be a closed safe Target : Prop with concrete definitions, no target axiom, free semantic predicate, assumed algorithm evaluator or placeholder. It must use the shared pinned LeanCert dependency in kernel mode, #assert_statement and #assert_trust kernel. Frozen-boundary Comparator identity and successful elaboration do not prove the mathematical target. A final boundary review must inspect every imported mathematical/model meaning. This symbolic target needs no floating-point experiments or artificial numerical certificate.

## Bound canonical and primary sources

| Raw source | SHA-256 |
| --- | --- |
| linear-systems-and-elimination/IE-12/README.md | a46926ac2cec003913f0ae71d3f4b54dfb44e82bb90daeaa3ab79ed757421b77 |
| linear-systems-and-elimination/IE-12/problem.tex | 47de5354e7d69a4baacc1dba21d2459225f3aad40ada819c6de681f13be6a755 |
| linear-systems-and-elimination/IE-12/solution.tex | 0ff18ae7048134695e191ec64d589f2828cc617596c4f2551662cdc8f84a6c07 |

## Exact target, constants and input domain

There exist one fixed finite randomized exact-real program P and two real constants C>0 and q>0 such that every natural n>=1, every nonsingular real n-by-n A with Euclidean operator norm ||A||_2=1, every real b in R^n with b!=0, and every real 0<epsilon<1/2 satisfy both requirements:

1. For every realization of the random streams, P returns a real n-vector x!=0 after at most C*n^2*epsilon^(-q) unit operations.
2. Under the independent random-stream law specified below, the output obeys
Pr{ ||A*x-b||_2 / (||A||_2*||x||_2) <= epsilon } >= 99/100.

The runtime is a deterministic bound over all draws, not an expected-time or high-probability bound. Successful termination and nonzero output are required even on the numerical-failure event. P,C,q precede every input and every draw. The exponent is the real power of the positive epsilon; its value is not fixed to q=3 merely because the resolution proves that value.

Nonsingularity means det(A)!=0. The operator norm is the genuine real Euclidean induced norm and vector norm is sqrt(sum of coordinate squares). A*x is the ordinary matrix-vector product. The division in the error ratio is by the positive original ||A||_2*||x||_2; it is not silently made true using a totalized zero denominator. The target concerns the original A and b, with perturbations in A only. No perturbation of b, forward error, condition-number promise, spectrum, symmetry, definiteness, or distributional assumption on the input is added.

## Concrete exact-real indexed machine

The binary Turing-machine model used for AV/IV bit complexity is not the model of IE-12. Use the following concrete scalar RAM description. It is fixed uniformly in the input dimension.

A program consists of a positive finite number L of labeled instructions, a finite number of real scratch registers, a positive finite number of natural address/counter registers (register 0 is the input-size register), and a finite table of real scalar constants. All program labels, scratch-register indices and constant indices are finite types. All instruction operands and successors are literal finite constructor data; a program is not a function that evaluates arbitrary input-dependent mathematical operations. Its finitely many real constants are fixed with the program and cannot depend on n,A,b,epsilon or the random draw. There is no advice function indexed by the input or dimension.

The state consists of a program label, the finite real and natural registers, an indexed real store M:Nat->Real, two natural random-stream cursors, and a running/successful-halt/failed tag. Only finitely many cells differ from the input-and-zero initial store after any finite trace. The natural registers are used for explicit indexing and loop counters, not as real-number digit extraction.

Permitted instruction constructors, each with an explicit next label unless it branches or halts, are:

- Load a fixed real constant, copy a real register, or assign to a real register the sum, difference, product or quotient of two real registers.
- Assign the nonnegative square root of a real register to a real register.
- Compare two real registers using < or = and branch to either of two fixed labels.
- Set a natural register to 0 or a fixed natural literal; copy it; increment it; decrement it with truncation at 0; add or multiply two natural registers; compare two natural registers by < or = and branch.
- Convert a natural register to its exact real value. There is no conversion of an arbitrary real register to a natural number and no floor, ceiling, logarithm, digit extraction, hash lookup by real value, spectral factorization or linear-solve instruction.
- Read M[a] into a real register or write a real register into M[a], where a is the natural value of one address register. This is ordinary integer-indexed scalar storage. Computing or changing an address uses the preceding charged counter instructions.
- Draw the next standard Gaussian value into a real register, incrementing the Gaussian cursor; or draw the next independent fair random bit into a real register as 0 or 1, incrementing the bit cursor.
- Unconditional jump to a fixed label, or successful halt returning the n consecutive entries beginning at an address held in a designated natural register.

Each instruction costs one unit, including comparisons, branching, each scalar-array read/write, address arithmetic, random draws and halt. Fixed natural-literal instructions and natural arithmetic are equivalent to the corresponding exact-real scalar arithmetic and comparisons on integer-valued counters up to absolute overhead. The natural type prevents an uncharged floor/digit primitive. This uses unit-cost scalar arithmetic, not a word-length or bit-cost bound.

Division by zero or square root of a negative operand sends the state to the distinct failed tag. Failed states do not return an output and cannot satisfy the runtime/return requirement. Branch labels and register indices are valid by their finite types. Reads from the unbounded natural-indexed store are always defined, defaulting to zero where no input or previous write is present. A run that loops or reaches failure on any draw does not meet the target.

The program has an initial label 0. Initially its natural input-size register is n, all other counter and real scratch registers and both stream cursors are zero, and the store contains A_ij at address i*n+j for 0<=i,j<n, b_i at n*n+i, and epsilon at n*n+n; all remaining cells are zero. Program literals supply fixed constants. The input is given in this ordinary dense layout with no precomputed factorization, advice or norm oracle; ||A||_2=1 is a promise and need not be tested. Initial availability of the input is free, as usual; every actual read is charged. Returning a pointer to n stored entries does not itself compute those entries. Charging an additional O(n) output serialization cost would be absorbed in the same target bound.

The finite program is permitted to use only Gaussian draws, only bit draws, both, or neither. Deterministic programs are therefore included. The two streams are concrete independent sources, not arbitrary sampled quantities supplied by a semantic oracle. Access is sequential through the cursor instruction; the program cannot inspect the full stream in one step.

## Random law and operational meaning of the statement

Use sample space Omega=(Nat->Real) times (Nat->Bool) with the product probability measure whose real coordinates are independent N(0,1) and whose Boolean coordinates are independent fair bits; the two coordinate families are independent of each other. Gaussian draws and random-bit draws each consume the next unused coordinate of their family at unit cost. This realizes independent draws even when the sequence of instruction types is chosen adaptively.

Define one deterministic transition function by structural case analysis on the actual instruction and state, and define the t-step state by ordinary natural iteration from the initial state. Successful-halt and failed tags are absorbing, but a successful runtime witness refers to the first or any already halted state reached within the bound. Halt returns the actual store slice as a vector Fin n->Real, not a caller-supplied output relation.

For every input in the stated domain and every omega, the first requirement is existence of t:Nat and x:Fin n->Real such that the t-step state is a successful halt returning x, x!=0, and (t:Real)<=C*(n:Real)^2*epsilon^(-q). No arbitrary runtime, correctness, probability or solver function is passed into Target.

The success event is the set of omega for which there exist such a bounded t and returned x also satisfying the displayed backward-error inequality. Since transitions are deterministic, different halted witnesses cannot change the returned output. The same concrete event is measured under the stream law and compared with exactly 99/100 in nonnegative extended reals (or by an explicitly order-preserving real conversion).

All primitive real operations and branch domains are Borel measurable. The index registers take countably many values and use concrete indexed reads; the finite-step state and every finite return event are measurable. The success event is a countable union over natural t of measurable events. No choice of a nonmeasurable solver or input-dependent probability law is needed. Proving these model properties is distinct from proving that a particular program meets the catalog target.

## Source resolution and preservation of scope

The complete canonical README and the archived Holden solution were inspected. The source's Problem/result section identifies exact-real scalar arithmetic, square roots, comparisons and Gaussian or bit draws. Its paragraph beginning "Indexed scalar-array reads and writes" explicitly states these may be counted at unit cost without changing the bound. The "Meaning of table access" remark says identifiers are integers built by charged loops/scalar arithmetic, with ordinary indexed storage; no input-specific advice or hashing is needed. This justifies the concrete indexed machine above rather than a black-box matrix-vector oracle.

The complete algorithm section and its "All realizations are well-defined" argument explicitly treat zero Gaussian denominators and a nonzero fallback output. Its iteration comparison and counters are charged, and it excludes expected-time qualifications. Thus all-draw bounded runtime and nonzero output are the faithful interpretation of the original "returns x!=0 ... using at most" requirement, not an extra success-probability relaxation.

The source proves a stronger theorem with q=3, error <=5*epsilon/8, success >0.997, O(n^2) storage, and even singular A. These statements explain the existing solved status but are not substituted for the original input domain, <=epsilon error, >=0.99 probability or existential exponent. The original target has no storage bound, so none is added. It asks total cost, not dimension-independent black-box iteration count; a log(n) total overhead cannot be hidden in a constant depending on epsilon.

The real constant pool is finite and globally fixed as in an exact-real arithmetic machine. It cannot encode a per-input response through a free evaluator; the only available accesses to a constant are the explicitly permitted operations and comparisons. If an implementation chooses a rational-only constant pool instead, its relation to this specification must be reviewed before treating the statement as identical. The exhibited source algorithm needs only rational constants and the listed operations, but that proof fact is not a reason to silently restrict the existential algorithm class.

## Before implementation

Independently review the instruction constructors, initialization and return convention, no-real-to-natural rule, charged indexed access, failure tags, random-stream law and universal worst-case trace bound before implementing the machine. The model needs a concrete Lean syntax and transition definition to state Target. It does not require first implementing the Holden solver, proving its rounding/filter estimates, deriving its exponent, or proving a compiler or complexity-composition theorem. Those are later proof obligations. The eventual shared exact-real model must be included in live/frozen import-closure hashes.

Preserve n=1, arbitrarily ill-conditioned nonsingular matrices, arbitrary nonzero right-hand-side magnitude and direction, epsilon approaching either open endpoint, Gaussian zero events and algorithmic numerical failures. No finite-precision rounding, approximate Gaussian sampler, expected cost or sampled input family is equivalent to this universal exact-real statement.
