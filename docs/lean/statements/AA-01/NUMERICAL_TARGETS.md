# AA-01 — exact decidability and rounded-tree specification

Specification author: OpenAI Codex AI agent `/root/inventory`, 2026-09-28.
This is a preimplementation specification. Two independent approvals are
required before implementing the model or the target. No decision procedure,
Lean target theorem or arithmetic evaluator is implemented by this document.

## Frozen identity and complete source

Permanent ID `AA-01`; canonical path
`arithmetic-and-complexity/AA-01/README.md`; campaign base
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`; retained status **Solved**.
`ORIGINAL.md` preserves the entire canonical README byte for byte, including
both credited resolutions, the exact original model, references and historical
audits. `source-lock.json` binds its raw SHA-256, problem.tex, the complete
retained Stepaniants solution and the complete retained Colbrook manuscript.
There is no existing local Lean source under this canonical problem directory.
No ID, canonical path, statement, status or attribution is changed.

The canonical question distinguishes an ordinary Turing decision algorithm
from a finite rounded arithmetic evaluator. Both will have concrete syntax
and semantics. The real signed-gap criterion is credited proof material; it
must not replace the existential evaluator predicate or become an assumed
oracle in the Turing machine.

## Explicit finite integer-polynomial input

A `PolynomialInput` consists of a natural number `n` and a finite list of
terms. Each term contains an integer coefficient `c` and an exponent vector
`a : Fin n -> Nat`. Its exact value at `x : Fin n -> Real` is

```text
PolynomialValue(input,x) = sum over all list occurrences (c:Real) * product_i (x_i ^ a_i).
```

The empty sum is zero and every zeroth power is one, including `0^0`. This is
an ordinary integer polynomial. A list may contain zero coefficients, repeated
exponent vectors or a noncanonical order; like terms are summed by the exact
polynomial semantics. Thus the decision must agree on lists representing the
same polynomial. No promise of homogeneity, positive degree of every listed
term, a particular zero set, or normalized support is imposed. `ValidInput`
means precisely `PolynomialValue(input, fun _ => 0)=0`, i.e. the collected
constant coefficient is zero. An equivalent finite integer sum of constant
coefficients may define this guard after its correspondence is checked.

The explicit binary encoding is

```text
encodeNat(n) ++ encodeNat(number of terms) ++
  concat in list order [encodeInt(c) ++ concat_{i in increasing Fin n} encodeNat(a_i)].
```

Use the existing reviewed `NLA.Computation.BinaryEncoding.encodeNat` and
`encodeInt`, including their fixed length framing and canonical signed-integer
representation. The two header fields determine every term boundary and the
number of exponents; no implicit dimension, coefficient bit, sign or exponent
is omitted. A sparse list is a concrete finite coefficient encoding, and dense
lists convert by exact finite integer operations. There is no complexity bound
requiring a polynomial-size translation between encoding conventions.
The integer coefficients, list counts and exponent indices are symbolic input
to the **Turing decision machine**. They are never free real constants or
initial registers of the rounded evaluator.

## Finite syntax with real registers and persistent reuse

Use an inductive finite syntax `Program r`, where `r` is the number of
currently available real registers. Its only constructors are:

```text
return(i : Fin r)                                  : Program r
negate(i : Fin r, next : Program(r+1))              : Program r
round(op : {add,subtract,multiply},
      i j : Fin r, next : Program(r+1))            : Program r
compare(i j : Fin r,
        less equal greater : Program r)           : Program r.
```

A complete evaluator on `n` inputs is `P : Program n`, initialized with
register vector exactly `x : Fin n -> Real`. No register is initialized to an
implicit zero, one, coefficient, tolerance, error variable or other constant.
At a negate or round constructor, append the new real value in register `r`;
all old registers retain their indices and values. A return selects a current
register. There is no implicit default output, unchecked index, failure output
mapped to zero, or unavailable-register read.

The `negate` node appends exactly `-rho[i]`. A `round` node appends
`(rho[i] op rho[j])*(1+delta_current)`. These are the only new numerical values.
Copies and storage are represented exactly by reusing the same existing index;
copy instructions need no separate arithmetic constructor. Reusing a stored
rounded result never recomputes it and never assigns it a fresh error.
Explicit exact negation creates an alias value without a rounding coordinate.

The `compare` node inspects the actual current real values `rho[i],rho[j]`
and selects the less, equal or greater continuation by exact real trichotomy.
All three branches begin with the same unchanged register vector. No numeric
zero/one is returned from the test; Boolean-to-real conversion is absent.
Comparisons may use raw inputs, negated values, stored rounded values or any
mixture, so outcomes may depend on errors. Equalities and ties must be retained.

This is a control-flow tree with persistent available values, not an arithmetic
formula in which every repeated occurrence is recomputed. All syntax, including
unselected branches, is finite. A finite program which overwrites named
registers can be represented by appending new versions and renaming later
references. Exact copying is aliasing; a finite bounded control flow can be
unrolled into this tree while retaining each path's stored values. Conversely
every constructor is an allowed canonical operation. These straightforward
syntax-correspondence obligations must be reviewed; an arbitrary semantic
function `Real^n -> Real` is not an alternative Program representation.

There is no recursion/loop constructor, arbitrary real literal, arbitrary
polynomial instruction, division, fused operation, exact addition or exact
multiplication/scaling. Integer coefficients can influence the finite tree's
shape and repeated operations, but not add forbidden primitive instructions.
The numbers zero and one in the mathematical error formula do not become
accessible program registers.

## Static error coordinates over the whole tree

Define the rounded-node count structurally:

```text
N(return i) = 0
N(negate i next) = N(next)
N(round op i j next) = 1 + N(next)
N(compare i j less equal greater) = N(less) + N(equal) + N(greater).
```

Errors for a whole program are `delta : Fin(N(P)) -> Real`. Number rounded
nodes by structural preorder, with less/equal/greater subtree order at each
comparison. The actual total real evaluation `Evaluate(P,rho,delta)` is
structural recursion on this finite syntax:

- At `return`, output `rho[i]` without reading errors.
- At `negate`, append the exact negative and pass the same error vector.
- At `round`, read coordinate zero for that node, append its rounded result,
  and pass the remaining vector with index shifted by one to the continuation.
- At `compare`, evaluate only the selected subtree. The less subtree receives
  coordinates `[0,N(less))`; equal receives the following `N(equal)` coordinates;
  greater receives the following `N(greater)` coordinates. The register vector
  is unchanged. In particular, a greater-branch node retains its static offset
  even though preceding branches were not executed.

Every distinct syntactic rounded node therefore has its own coordinate even
if its operands coincide with another node's operands. The coordinate is used
once when that node executes. Reading a stored value twice retains its already
chosen error dependence; it does not allocate two further coordinates. Errors
on unused branches are present in the universally quantified vector and ignored
by evaluation. `N(P)` is not merely the number of operations on the selected
path, and branch choice cannot renumber downstream static nodes.

One may implement the recursion using a natural-index error stream and explicit
offsets to simplify dependent types only if the public interpretation restricts
it to exactly these `N(P)` finite coordinates and proves/structurally exhibits
that no coordinate outside the assigned block is read. In particular, no
arbitrary input-dependent error function is supplied as an execution oracle.
The preferred public interface remains the finite-vector semantics above.

Errors are **arbitrary independent choices**, not random variables and not a
correctly-rounded floating-point function of the operands. There is no error
law requiring two equal operands to produce equal errors at distinct nodes,
no underflow/overflow exception, and no assumption about branch stability under
rounding. These features are all explicit in the source model.

## Exact accuracy and all-input uniformity

For a fixed input polynomial and fixed `P : Program input.n`, define
`Accurate(input,P)` as the conjunction

```text
(for every x:Real^n, Evaluate(P,x,zeroErrorVector) = PolynomialValue(input,x))
and
for every eta:Real, 0<eta -> eta<1 ->
  there exists u:Real, 0<u and u<1 and
  for every x:Real^n and every delta:Fin(N(P))->Real,
    (for every j, abs(delta[j])<=u) ->
      abs(Evaluate(P,x,delta)-PolynomialValue(input,x))
        <= eta*abs(PolynomialValue(input,x)).
```

The same finite tree precedes every `eta`. The precision `u` may depend on
that polynomial, that tree and `eta`, but not on `x` or the selected error
vector. The tree cannot read `eta`, `u` or any `delta` directly. All real
inputs are included, with no bounded domain, nonzero-output guard, genericity,
separation, excluded comparisons or finite test set. At every zero of the
polynomial the displayed inequality forces exactly zero output for every
permitted error vector. No absolute-error floor or additive tolerance is used.
Zero-error correctness concerns the **actual** zero-error path, not every
leaf's symbolic expression on inputs that never reach that leaf.

Set `AccuratelyEvaluable(input) := exists P : Program input.n, Accurate(input,P)`.
This existential is over finite syntax with the explicit evaluation just given,
not over a function assumed accurate by definition or a supplied analytic
criterion. A faithful statement need not implement a successful evaluator or
prove the signed-gap characterization.

## Zero-variable convention, explicitly resolved

The canonical README does not state `n>=1`. Both retained main treatments
start with `n>=1`, and the Colbrook manuscript's model-boundary paragraph
expressly discusses the possible zero-variable encoding. We retain natural
`n`, including zero, with the literal constant-free/output-register semantics.

When `n=0`, the origin is the unique empty input, every monomial is constant,
and `ValidInput` forces the polynomial to be zero. There is nevertheless no
`Program 0`: every constructor needs at least one `Fin 0` operand or output
index. Thus this degenerate valid coefficient list is a **no-instance**, not a
secret zero-output instruction. This agrees with the explicit retained source
boundary and can be decided separately without affecting the `n>=1` result.
For positive `n`, the zero polynomial is accurately computed by one rounded
subtraction `x_0-x_0`; all its error choices still return exactly zero.
No variable is silently adjoined to change the meaning of a zero-variable list.

## Original always-halting decision question

Use the existing reviewed `NLA.Computation.FiniteMachine` for the **ordinary
binary decision machine**, with its actual finite alphabet/control table,
TM0 transition semantics, terminality and one-bit output. Define exactly

```text
Target := exists M : FiniteMachine,
  for every input : PolynomialInput, ValidInput(input) ->
    exists answer : Bool, exists T : Nat,
      M.DecidesWithin (EncodePolynomial(input)) answer T
      and (answer = true iff AccuratelyEvaluable(input)).
```

The one finite machine is fixed before every integer-polynomial input.
`T` is only a finite halting-time witness and follows the particular input;
there is **no PolynomialBound**, complexity-class membership, degree cutoff,
or running-time guarantee. Every valid encoding must halt with exactly the
correct Boolean. Behavior on malformed words or lists with nonzero collected
constant coefficient is outside the stated input domain. No real-equality,
quantifier-elimination or tree-existence oracle is added to the binary machine.
The decision answer alone is required; outputting an evaluator is a separately
credited stronger result and is not added to Target.

## Source correspondence, proof work and numerical scope

The complete original and retained model sections were read. Stepaniants
Section 1 explicitly distinguishes the ordinary Turing procedure from the
rounded register/tree evaluator, gives exact copy/storage/comparison semantics
and all-branch error numbering, and Corollary 7.1 states the halting conclusion.
Colbrook Section 1 and its model-boundary discussion state the same model,
including the zero-variable convention. Their necessity arguments preserve
actual stored roots and error-dependent execution paths; neither allows
recomputing every reuse or treating comparison outcomes as numerical constants.

The primary [Demmel–Dumitriu–Holtz model, Sections 2.1–2.7](https://arxiv.org/html/math/0508350v2#S2)
was also checked: exact inputs, bounded finite evaluation, exact negation and
comparisons, arbitrary separate roundoff errors, and stored-result reuse match
the canonical restricted model. Its discussion also considers broader arithmetic
variants; those variants are not imported into this target.

The retained affirmative resolutions use finitely many signed ordering charts
and the coefficientwise absolute majorant of each **collected** transformed
polynomial, bounded uniformly by a chart constant times its absolute value
on the full nonnegative orthant. Prefix-gap versus suffix-gap charts differ
only by indexing convention. Expanding the coefficient list, collecting terms,
real quantifier elimination and constructing the constant-free evaluator are
later proof/algorithm work; none is an assumed theorem or primitive here.
If a later proof uses the criterion, taking coefficientwise absolute values
before collecting duplicate monomials would be incorrect. Reported experimental
programs missing from the source archive remain unverified provenance and are
not evidence for the new statement.

No numerical enumeration or interval certificate is needed to define this
exact question. Future kernel controls should check persistent reuse versus
independent recomputation, error-dependent equality branches, static offsets
past unused branches, exact negation, zero-error semantics, the positive-
dimension zero polynomial, and the absence of an output-producing `Program 0`.
For example, computing `v=round(x+x)` once and then `round(v*v)` must retain
`(1+delta_0)^2*(1+delta_1)`, not allocate a fresh error for each read of v.
These controls inspect operational meaning and cannot prove decidability.

## Review and Lean boundaries

Two independent reviews must approve these exact model, polynomial and
quantifier bytes before implementation. New shared finite-syntax helpers may
be used; do not change the previously reviewed ordinary finite machine or
binary primitives without reopening their review. The eventual safe closed
`NLA.Statements.AA01.Target : Prop` must use the shared pinned dependencies,
explicit LeanCert kernel trust, `#assert_statement`, `#assert_trust kernel`,
and an actual frozen-boundary equality check. Final reviewers must bind every
local helper import and pin and inspect that evaluation is structural and
finite. A type check, ordinary kernel control or Comparator identity does not
prove the decision theorem or alter the existing credits/status.

## Verbatim canonical target

<!-- canonical-target-start -->
## Problem statement

Consider finite arithmetic computation trees with exact real inputs
$`x\in\mathbb R^n`$. Arithmetic nodes use binary addition, subtraction, or
multiplication, each returning $`(a\mathbin{\circ}b)(1+\delta_j)`$.
Negation and comparisons ($`<,=,>`$) of available quantities are exact, and branching is
allowed. There are no constant input nodes. Each operation may have a different,
arbitrary error $`\delta_j`$; equal operands need not produce equal errors.
Previously computed values may be stored and reused. The tree describes
control flow, not a formula that recomputes each occurrence of a subexpression.

For $`p\in\mathbb Z[x_1,\ldots,x_n]`$ with $`p(0)=0`$, call such a tree $`P`$
accurate if $`P(x,0)=p(x)`$ and

```math
\forall\eta\in(0,1)\ \exists u\in(0,1)\quad
\forall x\in\mathbb R^n\ \forall\delta\in[-u,u]^{N(P)}:
\quad |P(x,\delta)-p(x)|\le\eta|p(x)|,
```

where $`N(P)`$ numbers all rounded nodes; errors on unused branches are ignored.
The same tree must work for every $`\eta`$, and $`u`$ may depend on $`p,P,\eta`$
but not on $`x`$. The condition includes exact output at zeros of $`p`$.

### Question

Is there a Turing algorithm which, from the finite integer
coefficient list of any such $`p`$, always halts and decides whether an accurate
tree exists? No bound on the decision algorithm's running time is prescribed.

This is a basic obstruction to automatically constructing accurate algorithms
for determinants and other polynomial expressions associated with structured
matrices. Checking a supplied fixed tree is already decidable; deciding whether
any suitable tree exists is the question.
<!-- canonical-target-end -->
