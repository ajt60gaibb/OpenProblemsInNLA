# AA-01 second independent proof review

Review date: 2026-09-11. **Verdict: PASS for the mathematical signed-gap characterization and its resulting decision procedure in the exact current canonical model.** No counterexample or material proof gap was found in the separated-execution, replay, interpolation, or constructive arguments. Recommend **Resolved** for the unchanged canonical AA-01 statement, subject to combining this audit with the other independent review. This is a mathematical Codex audit, not formal proof-assistant verification, journal peer review, or a publication-priority finding.

The empirical claims in the manuscript's reproduction section receive a narrower verdict: **not independently reproduced by this review**. The detailed programs described there are not present in the AA01 directory of the delivered bundle. The proof does not depend on their reported outcomes.

## Complete source identity and target

The entire source `.cache/colbrook-arithmetic/NLA_GitHub_submission_bundle/AA01_submission/manuscript.tex` was read, including the preamble, all sections and proofs, auxiliary face criterion, examples, model boundaries, numerical-test narrative, and references. Normalize by decoding UTF-8, replacing CRLF with LF, and re-encoding UTF-8, without trimming or removing final newlines. The complete normalized source has **41238 bytes** and SHA256 **`e34166543fea38668251b2b1307b6b29aac799f218aadd577c0280ed36610491`**. The manuscript is standalone; it includes no separate mathematical preamble whose hash is omitted.

The current `arithmetic-and-complexity/AA-01/README.md` was read in full. Its exact model is a fixed finite computation tree over exact real inputs, rounded binary addition/subtraction/multiplication with independently selectable occurrence errors, exact negation and comparisons of available quantities, stored-value reuse, no constant input nodes, and a whole-real-space relative-error guarantee uniform over inputs and all allowed error vectors. The input polynomial has integer coefficients and vanishes at zero. The desired conclusion is existence of an always-halting Turing decision procedure, with no complexity bound. The manuscript matches these requirements. A finite tree has a uniform finite bound on the number of rounded roots on every path; no unbounded loop model is silently admitted.

Locators: Theorem 1.1, line 122 (`thm:main`); constructive sufficiency, Section 2, line 143; separated execution Lemma 3.1, line 248 (`lem:sep`); primitive-form Lemma 3.2, line 297 (`lem:primitive`); replay Lemma 3.3, line 326 (`lem:replay`); interpolation Lemma 4.1, line 435 (`lem:interp`); necessity and Corollaries 4.2–4.3, Section 4; face criterion Proposition 5.1, line 518 (`prop:faces`); examples, Section 6; model boundaries, Section 7; reported verification, Section 8.

## Adversarial necessity: independent detailed audit

### Provenance normalization is valid in this model

At any point on an execution path, each available numeric value is an exact signed alias of an original input or a rounded arithmetic output. The only permitted exact numeric operation, negation, changes the sign of that alias. Assignment, reuse, branch selection, and a return statement select an existing value without creating an additional rounded occurrence. Consequently the finite root bound M=n+N(P) is valid even when branches contain many consecutive comparisons or terminate early. Comparisons do not return an unrestricted numeric constant or evaluate an uncomputed polynomial for free.

This distinction is essential and is maintained correctly: two independent arithmetic occurrences with identical operands produce distinct roots and may use different errors; two references to a stored output have one root and one previously chosen error. A positive and a negative alias of the same root are not falsely required to be separated from one another.

### Lemma 3.1: separated execution — PASS

Fix the input and 0<u<=1/4. All raw input roots are available before any rounded node, including inputs with zero or equal values. At a new arithmetic occurrence its operands, exact pre-rounding result b, and preceding roots are already determined along the path. Only its own multiplier s in [1-u/2,1+u/2] is chosen next.

If b=0, the rounded value remains zero for every multiplier. Against a nonzero root the separation ratio is exactly one, and a pair of zero roots is expressly exempt. Thus exact cancellation does not obstruct construction. If b is nonzero, dividing by b and setting r=w/b correctly reduces near-coincidence with an earlier root to s near a positive r. When r<=0, including r=0, the first strict bad inequality cannot occur because s>0. For r>0, the forbidden interval is `((1-gamma)r,r/(1-gamma))`. If it intersects the allowed s interval, then r<=3/[2(1-gamma)]<=2 for gamma<=1/4. Its length is at most `(16/3)gamma<6gamma`. Repeating for -w covers near-opposition as well as near-equality.

There are at most M earlier roots, so the union of both types of excluded intervals has length at most 12M gamma=3u/16, strictly less than the available length u. A permitted multiplier exists regardless of interval overlaps, signs, scales, repeated raw values, or previous branch choices. Relations among already chosen roots do not change. The next comparison selects a path according to these actual values, and finite control flow guarantees termination.

The selected errors may depend on the input and earlier choices. That is allowed: the accuracy hypothesis is universal over every error vector, not restricted to errors sampled independently in a probabilistic sense. Once the path is determined, unused errors can be filled arbitrarily to obtain a legal vector for the whole tree. No computable adversarial selection routine or uniform symbolic branch is required for this existential proof.

### Lemma 3.2: raw primitive forms — PASS, including chamber boundaries

For each signed-order chamber, a raw input is a signed prefix sum of nonnegative gaps. Any signed sum or difference of two such inputs is either the sum of two prefixes or the difference of nested prefixes. After choosing an overall sign, all its coefficients are nonnegative, in {0,1,2}. This includes identical inputs, repeated operands, opposite aliases, and a primitive form that vanishes identically. Consequently multiplying each gap by a number in [1-epsilon,1+epsilon] changes any such form by at most epsilon times its absolute original value.

If the original form vanishes, every contributing nonnegative gap term must vanish, so the perturbed form remains exactly zero. If it is nonzero, epsilon<1 preserves its sign. Hence raw-input comparisons and zero tests are stable even at zero coordinates or tied magnitudes; no generic-position assumption is hidden in the lemma. The transformed input stays in the same closed chamber because all perturbed gaps are nonnegative.

### Lemma 3.3: comparisons, arithmetic, and error budget — PASS

Replay proceeds along the old execution, holding every rounded root at its original numerical value while the raw inputs follow the perturbed gaps. A comparison between two raw roots is preserved by the preceding lemma. A comparison between two rounded roots is preserved because both signed values are fixed. A mixed comparison uses two distinct roots, so the separated execution guarantees a difference of magnitude at least gamma times their largest magnitude unless both are zero. Only the raw operand moves, by at most epsilon times its magnitude. Since epsilon/gamma=u/16<1, the comparison sign cannot change. The both-zero case remains an exact equality. Comparisons of a root with its own alias are covered by the raw/raw or rounded/rounded cases, not by an inapplicable distinct-root assumption.

The arithmetic cases are exhaustive:

- Two rounded operands remain fixed, so their exact sum, difference, or product is unchanged, including exact cancellation and zero products.
- Two raw operands under addition or subtraction give a signed primitive form, with relative change at most epsilon and exact preservation of zeros.
- Two nonzero raw operands under multiplication have relative product change at most 2epsilon+epsilon². This also covers squaring the same raw root; independent errors for two references are not assumed.
- A raw times rounded product has relative change at most epsilon, and a zero factor stays zero.
- A mixed sum or difference is nonzero unless both operands are zero, because both near-equality and near-opposition were excluded. Its relative change is at most epsilon/gamma.

Since gamma<1/3 and epsilon<1, the product bound is below 3epsilon<=epsilon/gamma. Thus every nonzero pre-rounding result b changes to b' with `|b'/b-1|<=theta=u/16`, while zeros stay zero. In particular, no nonzero b becomes zero.

For old output v=sb, choose s'=v/b' at a nonzero pre-result. This fixes the new root exactly. The estimate

`|s'-1| <= (u/2+theta)/(1-theta) = 9u/(16-u) <= 4u/7 < u`

is correct: the middle inequality is equivalent to u<=1/4. When b=b'=0, the old multiplier suffices. This leaves room inside the full allowed error box and does not assume the same error for different executions. Every future stored reuse sees exactly the held value; no fresh error is assigned to a stored alias. The induction works equally for an early return or an arithmetic-free path. A final signed rounded root is fixed, and a final signed raw input changes relatively by at most epsilon, proving the output statement.

### Uniform local bound and interpolation — PASS

Choose one tolerance eta=1/4 from the assumed uniform accuracy of the fixed program and shrink its u to at most 1/4. Then M, gamma, and epsilon are independent of the input, chart, and selected path. For every y and every perturbation t in the fixed multiplicative box, the adversarial execution and its replay are both covered by the universal accuracy assumption. They give

`|p(x')| <= (4/3)|V'| <= (4/3)(1+epsilon)|V| <= (5/3)(1+epsilon)|p(x)| <= 2|p(x)|`.

No division by p(x) occurs. This remains valid at polynomial zeros and forces the corresponding nearby gap box to be zero as well. The rounded execution may reach a leaf that is not reachable at zero error; the proof never substitutes a zero-error branch identity at that leaf. This avoids a substantial potential failure mode of branching-program arguments.

For each fixed y, Q_y(t)=q(y_1t_1,...,y_nt_n) has coefficients c_alpha y^alpha. The tensor-product Vandermonde grid has D+1 distinct nodes in each coordinate, so its coefficient-to-value map is invertible. Taking the sum of absolute entries of the inverse gives a finite K independent of y, the chart, and the polynomial's particular coefficient values. Since y>=0, the coefficient l1 norm is exactly q#(y), even with zero coordinates. The uniform local bound therefore proves `q#(y)<=2K|q(y)|` globally on the closed orthant. The degree bound D=deg p is sufficient because the linear coordinate map cannot increase total degree. The zero polynomial is correctly treated separately.

The same argument with any one fixed eta0<1 gives a finite local factor `(1+eta0)(1+epsilon)/(1-eta0)`, proving the stated one-tolerance corollary. It does not claim that the original tree becomes accurate for every tolerance; it constructs a new canonical evaluator from the resulting criterion.

## Sufficiency and decidability

The constructive direction uses only permitted operations. Input signs are found by comparing x_i with -x_i, without introducing zero as a numeric input. Absolute magnitudes are exact aliases, and their sorting is a finite comparison tree. Each gap after the first is computed by a single rounded subtraction of two original magnitudes, so it has its own relative error and a zero gap remains exactly zero. This is consistent with the stipulated relative-operation model, irrespective of cancellation size; no IEEE rounding or underflow assumption is imported.

Every nonzero monomial has positive degree because p(0)=0 and the chart is linear. Thus it can start from an available gap, form powers and products, and realize integer coefficients by a finite number of additions, with exact negation for negative coefficients. No constant one input is needed. Repeated stored factors produce repeated occurrences of the same error multiplier in symbolic expressions, which the finite factor count R explicitly permits. Each collected monomial's contributions have one sign, so after all additions its relative coefficient perturbation is bounded by a positive weighted average of products of at most R factors. Final cancellation between distinct monomials is controlled by the coefficient majorant, not assumed harmless.

For u<=1/(2R), both `(1+u)^R-1` and `1-(1-u)^R` are at most 2Ru. The error is therefore at most 2Ru q#(y)<=2CRu|q(y)|. Choosing the finite maxima of C,R over chambers and u<=eta/(2CR) supplies the uniform quantifiers of the canonical definition. It also forces exact output whenever p vanishes. The p=0 evaluator x1-x1 is legal and exact. The text explicitly separates the degenerate zero-input-variable encoding, if admitted; this does not leave undecidability in that case.

The decision sentence uses only integer polynomial equalities/inequalities, existential C>=1, and universal real y constrained to be nonnegative. Squaring is equivalent to the desired inequality on that domain. There are finitely many charts and their expansions are computable from the finite integer coefficient list. Effective real quantifier elimination therefore gives an always-halting Turing procedure. A successful instance can obtain an integer C by successive exact decisions, since any real bound can be enlarged to an integer. No practical complexity, bounded-resource solver, or search over arbitrary trees is required.

## Auxiliary face criterion and examples

Proposition 5.1 was checked separately. A positive zero of an exposed face polynomial produces a ratio tending to zero along its exponential monomial curve, including the whole-face case. Conversely, failure of domination on the closed orthant also occurs on the positive orthant by continuity. Normalized monomial weights have a convergent subsequence in a compact simplex. For the positive limiting support T, projecting log inputs onto the span of its exponent differences gives a convergent projected vector because all the corresponding log weight ratios converge. The complementary projection makes every outside log ratio tend to negative infinity. One sufficiently late projection vector therefore exposes exactly T as a face, rather than an arbitrary subset of a face. The remaining limiting weights are positive exponential-family weights on T and their signed sum zero yields the required positive face zero. This argument handles unbounded scales in different directions without assuming a single normalized direction converges to a sufficiently discriminating normal.

The selector-based existential formula correctly requires equality on all selected exponents and strict inequality on every unselected exponent. Integer exposing normals exist because the finite linear face constraints have rational coefficients, and real-algebraic positive zero witnesses exist by the real closed field property. With an integer normal, factoring t^(-b) leaves nonnegative integer exponents b-alpha dot v, so the displayed Q,H really are polynomials and H(0)>0.

The displayed difference-of-squares and three-term-sum examples follow directly from the charts. The isolated-zero example has p(t,t²)=t^6 and majorant excess 4t^4, confirming failure of a bounded ratio despite an allowable isolated zero. In the Motzkin middle chart, expanding the displayed squares on the certificate's right side gives coefficient 2c for every positive coefficient c of q and 4c for each negative coefficient, exactly matching 3q-q#. All displayed certificate summands are nonnegative on the orthant. The additional family F²+FG+G² has the stated coefficient-majorant bound, and opposite signs give the exact nonnegative remainder 2(U-V)². These supporting arguments are consistent with the main criterion; finite test counts are not needed to establish it.

## Primary-source comparison and explicit limitations

The [Demmel–Dumitriu–Holtz primary paper, Sections 2.2–2.7 and 4.3](https://arxiv.org/pdf/math/0508350v2) distinguishes exact inputs, finite computations, independent occurrence errors, branching, and constants, and leaves the general real-case route incomplete. The [Acta Numerica survey, Section 3.3.7](https://people.eecs.berkeley.edu/~demmel/Demmel_pubs_07_11_final/B15_ActaNumerica08.pdf) discusses obstacles to a complete procedure. The submitted proof addresses the precise whole-real-space constant-free finite-tree specialization of that question fixed by the canonical. Its face-support mechanism agrees with the closure geometry discussed by [Rauh–Kahle–Ay, Section 2](https://arxiv.org/pdf/0906.5462v2), but the manuscript includes its own sufficient proof of that auxiliary fact.

The verified theorem does not extend without further work to variable-length adaptive loops, restricted domains not preserved by gap changes, division, fused multiply-add, exact nontrivial scaling, arbitrary polynomial black boxes, nonzero numeric constant inputs, bit access, or correctly rounded IEEE arithmetic. The adversary uses arbitrary independently choosable errors; it is not a claim about a particular hardware rounding function. Exact comparisons are comparisons of available values, not an oracle for unevaluated polynomial signs.

The AA01 directory actually supplies the manuscript/PDF, an issue draft, and two JSON logs. This review did not find the many detailed separation, replay, compiler, solver, or algebraic-certificate programs described in Section 8 in the delivered bundle. Their run counts, R=36 for the reported Motzkin compiler, and model-export claims cannot be independently reproduced from these files here. The mathematical theorem only needs some finite factor count for the explicit construction and the standard terminating real-algebraic decision theorem; it does not depend on those specific implementation claims. Archive or rendered metadata should distinguish mathematical PASS from reproduction of all reported experiments.

**Final disposition: PASS for Theorem 1.1 and the full canonical AA-01 decision question, with the auxiliary mathematical claims checked as above. No material mathematical gap or required source edit was identified. The reported historical test campaigns are not independently certified, and no priority or broader-model claim is made.**
