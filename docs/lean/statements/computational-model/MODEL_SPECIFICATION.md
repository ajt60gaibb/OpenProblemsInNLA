# Concrete binary computation model for complexity statements

Author: OpenAI Codex AI agent `/root/inventory`, 2026-09-28.

Status: **proposed mathematical and implementation specification, awaiting two independent reviews**. No Lean module, complexity theorem, algorithm or reduction is implemented here. This proposal applies first to AV-01, AV-02 and IV-05. Their complete original pages and reviewed per-ID specifications remain controlling inputs.

## Finding and recommended foundation

Use a finite instance of Mathlib's actual `Turing.TM0` transition system for ordinary bit algorithms, with a fixed three-symbol tape alphabet and a finite transition table. Add a separately specified finite oracle-machine extension for AV-02. Define polynomial time by the number of concrete machine transitions on the explicitly encoded input. Do not quantify over an arbitrary encoding, transition function on unlimited mathematical data, or cost function.

The inspected Mathlib checkout is exactly `0df444a360eaa60ab8c11dca51a86af692955474`, matching the shared campaign pin. The local checkout was `/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib`. The accompanying `source-audit.json` records exact inspected source hashes and the bounded API search. Primary source links below refer to that same immutable revision.

| Existing source | What is available | Important limit |
| --- | --- | --- |
| [PostTuringMachine.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/PostTuringMachine.lean) | `Turing.TM0.Machine`, `Stmt`, `Cfg`, `step`, `init`; each instruction moves one cell or writes one symbol. | The unbundled model permits infinite state/alphabet types. The campaign must instantiate finite types. |
| [Tape.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Tape.lean) | Concrete tape, movement, writing and finite-support/list representations. | Output convention and binary alphabet inclusion must be fixed, not supplied by the target. |
| [StateTransition.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/StateTransition.lean) | `EvalsTo` and `EvalsToInTime` record an actual finite iteration and its step bound. | Reaching a configuration is not itself halting. A terminal-state condition must also be required. These are witness structures, so a proposition uses their `Nonempty` form or an explicit existential trace. |
| [Computable.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean) | `FinTM2`, `TM2OutputsInTime`, `TM2ComputableInPolyTime`. | The bundled machine explicitly gives finiteness for the input alphabet only. The composition result is `proof_wanted`, not an available proof. |
| [Encoding.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/Encoding.lean) | `Computability.Encoding`, binary natural/Boolean encodings, list and product constructions. | Encode/decode inversion does not imply efficient encoding. An arbitrary encoding can hide an answer or use exponentially longer unary strings. |
| [StackTuringMachine.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/StackTuringMachine.lean) | Concrete TM2 stack operations and simulations to TM1. | A TM2 step executes a finite program block. The discussed polynomial simulation overhead is not exposed as a proved quantitative time theorem in the inspected material. |

The bounded search found no definitions of the classes NP/coNP, NP-hardness, polynomial many-one reduction, or promise-preserving polynomial oracle reduction. Nondeterministic finite automata are not an NP complexity API. `Partrec` and its machine translations supply computability machinery, but a computability theorem alone does not establish polynomial bit complexity.

`TM2ComputableInPolyTime.comp` must not be imported as if proved. Its `proof_wanted` declaration uses the Batteries wanted-declaration mechanism, which records an unmet proposition without furnishing a proof or mathematical axiom. No wanted hypothesis may be silently added to a catalog target.

## 1. Ordinary finite machine and exact runtime

Let `Word = List Bool`. Fix the tape alphabet to `Option Bool`: `none` is blank, and `some false` and `some true` are the two bit symbols. No real number, rational, unbounded integer, list, predicate, or oracle is one tape symbol.

An ordinary machine consists of a natural number `s`, state type `Fin (s+1)` with initial state zero, and the complete finite table

\[
\delta : \operatorname{Fin}(s+1)\times\operatorname{Option}(\mathrm{Bool})
\longrightarrow
\operatorname{Option}\bigl(\operatorname{Fin}(s+1)\times\mathrm{TM0.Stmt}\bigr).
\]

The table uses Mathlib's existing `TM0.Stmt`: move left, move right, or write one alphabet symbol. `none` means halt. The table is chosen once before all inputs. Its size may depend on the algorithm, never on the instance. A function on this fixed finite domain is a finite table, not an infinite-data oracle. If implementation uses functions to represent tables, document this finite-domain fact explicitly.

Initial configuration is `TM0.init (w.map some)`. All cells outside the finite input are blank. A final output word `v` is represented by the finite bit string to the right of the final head, including the current cell, followed by blanks: the corresponding `ListBlank` is exactly `ListBlank.mk (v.map some)`. This representation is injective because bit symbols are never blank. Tape contents to the left of the final head are irrelevant. The empty output is permitted for a general transducer; a decision machine must output exactly `[false]` or `[true]`.

Define `RunsWithin(M,w,v,T)` as existence of a final configuration `c` and an actual sequence of at most `T` applications of **the fixed `TM0.step M`**, starting at the initial configuration, such that `step M c = none` and `c` has output `v` in the stated convention. It can be expressed through `Nonempty (StateTransition.EvalsToInTime ... (some c) T)` plus the halt/output conditions. Reaching `none` is not an output value and must not be mistaken for divergence or acceptance.

For every polynomial-time target, quantify one machine and natural constants `C >= 1`, `k`, before every instance, and use

\[
T(w)=C(|w|+1)^k.
\]

There is no supplied `cost : Input -> Nat`, no asserted evaluator relation, and no callback able to inspect an entire unbounded input in one transition. The finite transition table can examine only the current head symbol and state. Ordinary arithmetic, comparisons of long integers, matrix construction, parsing and output writing must occur through these transitions when a proof later constructs an algorithm. Output length is bounded by the finite input region plus newly visited/written cells; it is not a free unbounded return value.

### Optional TM2 implementation route

TM2 can remain a useful development language, but it must not change the statement's meaning. An alternative wrapper must require all stack indices, labels, internal states **and every stack alphabet** to be finite. Each program block is a finite syntax tree; the maximum number of primitive actions in a block is a machine-dependent constant. No register holding an arbitrary natural/rational/real value is finite internal state. Quantified encoders remain the explicit encoders below.

To substitute this wrapper for the chosen TM0 definition, supply a reviewed polynomial-time simulation theorem, including input/output handling and any stack cleanup. Mathlib's `haltList` requires the initial internal state and empty non-output stacks; that stronger final form needs a costed cleanup argument. The currently available reachability simulations are not themselves such a runtime theorem. The simplest first statement implementation avoids this optional equivalence by using finite TM0 directly.

## 2. Fixed rational and matrix input encodings

Use the following concrete, prefix-decodable binary grammar. These definitions are fixed shared library data, never existential parameters in a problem statement.

1. Let `bin(a)` be the usual most-significant-bit-first binary numeral of a natural `a`, with `bin(0)=[false]`, and no leading zero otherwise. Let `L` be its length, so `L >= 1`.
2. Encode a natural as `true` repeated `L` times, then `false`, then the `L` bits of `bin(a)`. Its length is exactly `2L+1`. The prefix is unary in **bit length**, not unary in `a`.
3. Encode an integer by a sign bit followed by the natural encoding of its absolute value. Sign false means nonnegative; reject the noncanonical negative-zero representation.
4. Encode a rational by its signed normalized numerator followed by its positive denominator. Require denominator positive and numerator/denominator coprime, using the canonical normalized rational representation. Zero has numerator zero and denominator one.
5. Encode a square matrix instance by its dimension followed by the explicitly listed rational coefficients in fixed row-major order, then the explicitly listed RHS/threshold data. The dimension determines the number of entries; all data must be consumed, with no ignored suffix.

The specific three input words are:

| Target | Exact field order after the dimension |
| --- | --- |
| AV-01 | `A` in row-major order, then `b` in coordinate order. |
| AV-02 | `A` in row-major order, then rational threshold `t`. |
| IV-05 | `L`, then `U`, each row-major; then lower RHS `l`, then upper RHS `u`. |

Dimensions and every numerator/denominator bit contribute to length. Matrices are dense explicit input unless an individual canonical problem expressly says otherwise. In particular a large dimension cannot hide an omitted zero matrix in a short symbolic input.

Define parser/decoder functions by this grammar, returning `Option` and rejecting malformed/extra/noncanonical syntax. Matrix dimension positivity, threshold positivity, endpoint order and the real regularity/inverse-M promise are separate predicates. No parser may evaluate the real solution predicate or recognize the analytic promise for free. The rational syntax, shape and endpoint inequalities are decidable; the analytic promises need not be decided by an algorithm in the target.

If reusing `Computability.encodeNat`, record its observed least-significant-bit-first convention and empty word for zero, and prove the concrete conversion to this chosen convention. It cannot be silently substituted for the grammar just specified. Either convention can be the final reviewed one; changing it changes source bytes and reopens the relevant reviews.

### Encoding equivalence obligations

Before claiming equivalence to conventional binary input rather than merely presenting a chosen model, verify:

- Encode/decode inversion, uniqueness of the canonical representation, correct sign/denominator normalization, exact matrix shape and row-major order.
- Polynomial translations in both directions between this framed encoding and the standard signed-numerator/positive-denominator representation used in the canonical problems. Include gcd normalization if accepting unreduced fractions; no leading-zero or unreduced-input issue may remove a legal instance.
- Polynomial-time syntactic recognition if the language is extended to reject all malformed words. A parser must reject impossible matrix lengths before attempting an exponentially large allocation based on a short dimension field.
- Length comparison with the sum of dimension and rational bit lengths. A scalar prefix has only constant-factor bit-length overhead; there is no unary integer encoding.
- Exact rational output decoding, including every output component's bit length. The IV-05 output grammar is `encNat(n)`, then the `n` lower endpoints in coordinate order, then the `n` upper endpoints in coordinate order, each endpoint using the rational grammar above. The output dimension must equal the input dimension, and the decoder consumes the complete output with no suffix.

These are model-correspondence obligations, not assumptions supplied to a target. They must be proved when needed or left explicitly pending. An abstract `Encoding` with a left inverse alone is insufficient: it could append an already computed answer to its input.

## 3. Uniform decision and function classes

For a concrete encoder `enc` and a semantic predicate `P` on input objects, the direct encoded-input statement is

\[
\exists M,C\ge1,k\quad\forall a\in D,\quad
\exists b\in\{\mathrm{false},\mathrm{true}\}:\
\operatorname{RunsWithin}(M,\operatorname{enc}(a),[b],C(|\operatorname{enc}(a)|+1)^k)
\ \land\ (b=\mathrm{true}\leftrightarrow P(a)).
\]

Here `D` is the original input domain, not an additional convenient promise. For AV-01 it consists of every rational `n,A,b` with `n>=1`; `P(a)` is exactly the bijection/cardinality predicate in its reviewed spec. No promise of finitely many solutions is allowed.

For a promised exact-output problem, replace `[b]` by a concrete rational output encoding and require its decoded output relation. IV-05 uses the reviewed coordinate enclosure **and separate attainment** conditions, with the original inverse-M promise in `D`. Off-promise behavior, including nontermination, is unrestricted. Uniform constants still precede all promised inputs; the promise cannot determine a different machine.

If an ordinary language `InP : Set Word -> Prop` is needed, require the finite machine to halt on **every** binary word and decide language membership. Use the fixed polynomial syntactic recognizer to prove the bridge from the encoded-input convention when malformed words are designated negative. Do not silently strengthen an unrestricted-off-promise target to one that decides its promise.

## 4. Concrete NP and many-one reductions

An NP language is a set `L` of binary words for which there exist a finite ordinary verifier machine `V` and fixed natural polynomial bounds `p` and `q` with this behavior:

\[
w\in L\quad\Longleftrightarrow\quad
\exists c:\ |c|\le p(|w|)\ \land\ V(\operatorname{pair}(w,c))\text{ returns true}.
\]

`pair(w,c)` is the fixed word encoding `encNat(|w|) ++ w ++ encNat(|c|) ++ c`, with exact declared lengths and no ignored suffix. The verifier halts with a Boolean output on every pair within `q(|pair(w,c)|)`, counted by the ordinary machine relation above. Both bounds have the explicit natural-constant form. Certificates are ordinary binary strings, not arbitrary real/rational objects with a free semantic predicate. Acceptance means an actual bounded run of `V`; a freely supplied verification relation is insufficient.

This conventional polynomial-certificate definition directly specifies NP. A theorem equating it to a nondeterministic machine model is useful infrastructure but not necessary just to define a faithful NP-hardness target. Define coNP by complement membership in NP. No assumption that P differs from NP is introduced.

A polynomial many-one reduction `L <=m K` means existence of one ordinary finite transducer, with a uniform polynomial time bound, which outputs a word `f(w)` on every `w` and satisfies `w in L iff f(w) in K`. The map is determined by the machine run; it is not an arbitrary function accompanied by a chosen fake cost. For a promise target, additionally require every output to be a legal promised instance. A proof from an NP-complete source requires the source's completeness theorem; the **statement** of universal NP-hardness does not.

## 5. Explicit promise-preserving oracle reductions

AV-02 requests a genuine Turing reduction, so a many-one-only predicate is not the original statement. Add a finite oracle machine with three tapes over the same finite alphabet: a main input/work/output tape, an additional work tape, and a designated query tape. The program has finitely many control states. Its ordinary transition table depends only on the control state and the three current head symbols; one ordinary transition applies at most one TM0 move/write action to each tape and changes control state. Three simultaneous bounded actions differ from a sequential conventional step by a fixed constant, with a straightforward correspondence obligation.

Use state type `Fin (s+1)` with initial state zero. On input `w`, initialize the main tape to `Tape.mk₁ (w.map some)`, and each of the other two tapes to `Tape.mk₁ []`; all three heads are at these designated origins. The successful final output is read from the main tape by exactly the ordinary output convention in Section 1, with a Boolean decision output restricted to a single bit.

The only additional instruction is an explicit **query** action with fixed yes/no continuation states. It takes the finite contiguous binary word currently on the query tape, at its designated current start head, calls `O : Word -> Bool`, leaves all tape contents unchanged, and selects the corresponding continuation. The representation is the equality of the query tape's current right-hand `ListBlank` with `ListBlank.mk (v.map some)` for the unique word `v`; left-hand contents are irrelevant. This query costs one transition in the conventional oracle model. Forming the query, copying bits, moving to its start, and later clearing/reusing it all require counted ordinary transitions. No instruction can query an arbitrary function of the whole input, evaluate a real norm, write an unlimited answer, or read the oracle except at this action. A query trace records the concrete word and pre-query configuration.

Distinguish a successful `halt` instruction from a malformed query-tape **failure** outcome. Failure is a separate tagged terminal outcome and can never satisfy successful halting, acceptance or output, even if the main tape already contains an apparent output bit. In particular, do not represent both successful halt and malformed-query failure merely by the same unqualified `step = none` test. A query word with valid tape representation but outside the mathematical problem's promise is different: its oracle answer is allowed to be arbitrary, and the reduction's separate every-query-legality condition prohibits that query in any required run.

The explicit two-work-tape extension is a proposed new concrete semantic definition; Mathlib currently supplies the tape primitives but not this oracle API. Its step function must be defined by the finite table and query action, not accepted as a free parameter. Before using another oracle-machine model, review a polynomial simulation including query construction and legal-query correspondence.

For AV-02 define:

- `Legal(v)`: `v` is the fixed encoding of `n>=1`, rational `A`, positive rational `t`, and every real perturbation `A-diag(d)` for `d in [-1,1]^n` is nonsingular.
- `Yes(v)` on legal words: the exact Euclidean spectral-norm threshold `c2(A)>=t` from the reviewed specification. The maximum/existential formulation must use the reviewed compactness/regularity correspondence, not a singular totalized inverse.
- `Compatible(O)`: for every legal word, `O(v)=true iff Yes(v)`. Outside the legal domain, both Boolean answers are allowed.

The requested hardness proposition is:

\[
\forall L,\ \operatorname{NP}(L)\ \Longrightarrow\
\exists R,C\ge1,k,\ \forall O,\ \operatorname{Compatible}(O)\ \Longrightarrow\
\forall w,\ R^O(w)\text{ halts within }C(|w|+1)^k\text{ and decides }L(w),
\]

**and every query in every such run is legal.** Put the time, output and query-legality clauses in the same quantified run property. Machine and constants precede the compatible oracle and input. Do not require a promise-recognition routine, permit off-promise guesses, restrict to a single favorable oracle, or make runtime depend on an oracle-specific constant. Clocking to force polynomial termination for arbitrary incompatible oracles is an optional equivalence lemma, not an unannounced stronger premise.

The mathematical function `O` is intentional only in this genuine oracle-reduction model. It is not available as a unit-cost LP solver or spectral-norm evaluator inside AV-01/IV-05 ordinary machines. Query length is physically bounded by what finite transitions can write, even though answering a completed query is one oracle step.

## 6. What must exist for a statement, and what belongs to a proof

| Required for a complete, reviewed Lean statement | Needed only to prove a resolution using the advertised algorithm |
| --- | --- |
| Concrete finite machines, actual step function, initialization, halting and output decoding. | Construction of the particular LP/linear-algebra machine and its correctness proof. |
| Fixed explicit binary/rational/matrix encoders and the relevant model-correspondence checks. | Polynomial gcd, rational arithmetic, inversion, LP and composition bounds used by that construction. |
| A uniform polynomial bound expressed through actual transitions. | A witness machine meeting that bound. |
| Concrete certificate-verifier NP and concrete promise-safe oracle semantics for AV-02. | MAX-CUT NP-completeness, the matrix reduction, its size/time bound and threshold separation. |
| Exact original matrix/solution/norm/hull predicates and domains. | Analytic characterization, LP equivalence, extremizer existence and other proof lemmas. |

Thus a missing formal rational-LP solver does **not** prevent a faithful statement of “there exists a polynomial-time machine.” Neither does the missing Mathlib composition proof. Both prevent certain complete resolution proofs, which are outside this statement-only campaign. The per-ID dependency paragraphs have been amended to make this distinction explicit; those amended files require reviews bound to their final hashes. Missing complexity theorems must not be replaced by an assumed LP oracle.

No LeanCert numerical calculation is needed for these definitions. If a future reduction proof needs a numerical inequality, use the shared pinned kernel mode; a certified scalar bound alone is not a proof of machine runtime or NP-hardness.

## 7. Review and implementation sequence

1. Obtain two independent reviews of this exact model, particularly the finite-domain restrictions, halting convention, framing grammar, certificate bound and every oracle quantifier.
2. Implement ordinary finite TM0 wrappers, concrete encoders and bounded-run predicates. Verify semantic regression examples: empty word, zero/negative rational encodings, denominator zero, truncated/extra fields, a halting versus merely reached state, and exact output length. These examples test definitions, not solve catalog problems.
3. Independently review their full Lean definitions/import closure and prove the needed elementary encoding/model correspondence. Implement AV-01 and IV-05 `Prop` targets using their original semantic predicates; do not build an LP algorithm solely to state them.
4. Implement/review concrete NP verifier and oracle-machine extensions, including query trace legality and a malformed-query rejection example. Then implement AV-02's universal hardness proposition.
5. Bind model sources, fixed encoders and dependency pins in every importing problem's Lean-boundary review. A model change reopens every affected review; frozen target equality alone cannot hide changed shared semantics.

This model is reusable for ordinary polynomial **binary-time** or unbounded decidability questions after per-ID review. It does not automatically apply to arithmetic-operation counts, bit-precision-sensitive sharp exponents, randomized success probabilities, real-number oracle models, or matvec query complexity. Those canonical targets need their own concrete cost/interaction semantics; a polynomially equivalent machine can change a sharp exponent and therefore cannot be substituted indiscriminately.
