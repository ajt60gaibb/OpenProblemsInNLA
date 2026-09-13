# IV-06 PR 193 independent semantic and proof cross-review

**Verdict: PASS. No mathematical or statement-correspondence blocker found.**

Reviewed head: `f73edd6c6562a78d1c4f56fdc4c1c75dac9ace4a` in the read-only checkout `/private/tmp/nla-audit-193` on 12 September 2026. This review independently read the full `Definitions.lean`, `Proof.lean`, `Challenge.lean`, and `Solution.lean`, the canonical original problem statement, and Colbrook's complete original counterexample manuscript. It supplements the root reviewer's authenticated Linux kernel/Comparator/control and axiom checks; it does not claim a new Lean build or CI run.

## Target and independent-entry semantics

`RealMatrix n` is the actual real square-matrix type, and `EntrywiseLE` independently quantifies all row/column pairs. `InIntervalFamily` is the conjunction of the two endpoint comparisons. There is no symmetry, diagonalizability, spectrum-reality, matrix-coupling, or finiteness condition.

The positive-dimensional conjecture universally quantifies `n`, `L`, and `U` and assumes only `1 <= n` and `L <= U` entrywise. It bounds the actual cardinality of the actual connected-component quotient of the real eigenvalue set. This matches the canonical original component-count question. The theorem need not formalize the optional equivalent interval-cover wording to refute that question.

`interval_family_iff` (Proof lines 40–57) proves equality with the full independent-entry endpoint box. In the forward direction it extracts the two unrestricted entries and forces all seven singleton entries using both bounds. The reverse direction checks every entry. Thus the counterexample is not restricted to an unproved parameterized subfamily, and no diagonal/symmetric coupling is introduced.

## Eigenvectors, determinants, and separators

`HasRealEigenvalue` explicitly requires an actual vector `v != 0` and `A.mulVec v = lam • v`. `realEigenvalueSet` existentially quantifies an admissible matrix and that genuine eigenpair. `characteristicDet` is `Matrix.det (lam • 1 - A)`.

The generic determinant/eigenvector bridge (Proof lines 25–37) uses the actual singular-matrix kernel equivalence and rewrites the action of `lam I-A`; it neither assumes an eigenvalue convention nor replaces the determinant with a polynomial declaration. Its extra dimension-zero endpoint is harmless: there is no nonzero vector and the empty determinant is one.

The all-real determinant polynomial (lines 60–65) is expanded from the actual matrix determinant. Each of the four witness memberships (lines 77–97) is backed by interval admissibility, a proved nonzero first coordinate, and an actual matrix-vector equation. In particular, the zero eigenvalue witness is not lost by a nonzero-eigenvalue condition.

All separator bounds (lines 104–127) quantify every admissible matrix. The determinant is affine in the two free parameters, and exact linear arithmetic derives the stated bounds from all four endpoint inequalities. The explicit kernel LeanCert proof of `-18 < 0` is used by the strict upper-sign chain, which feeds each exclusion and the final contradiction. The argument requires no eigenvalue approximation, numerical root isolation, or interval subdivision.

Independently of supplied diagnostics, I recomputed the symbolic three-variable determinant, all four exact integer eigenpairs and interval memberships, and all twelve separator-corner determinants with exact SymPy arithmetic. The separator intervals are exactly `[-332,-32]`, `[-318,-18]`, and `[-3750,-150]`. Results are saved in `/private/tmp/nla-pr193-cross-checks.json`.

## Actual topology and cardinality

The supplied pinned Mathlib `Clopen.lean` source at `/private/tmp/nla-iv06-pinned-Clopen.lean`, lines 502–530, defines `ConnectedComponents` as the quotient by equality of actual `connectedComponent` sets. Its `coe_eq_coe'` gives membership in the same actual component. This is not a custom quotient by spectral labels or a quasi-component substitute.

In `connected_component_intervals_proved` (Proof lines 131–142), `S : Set ℝ` is used as its real subtype, with the inherited topology. Equality of quotient classes places `x` in the component of `y` inside that subtype. The component is preconnected, its image under the continuous subtype inclusion is preconnected in the real line, and both real endpoints belong to that image. `Icc_subset` therefore contains every intermediate real number; unpacking the image witness yields actual membership in `S`. No closedness, compactness, finite-component, or path-connectedness assumption is needed. If endpoints are reversed the interval statement is vacuous, which is harmless because every subsequent use has the required increasing order.

`ordered_pair_separator` supplies an excluded number between every ordered pair of distinct witness indices. The four component classes are proved pairwise distinct, using trichotomy to reverse the order where necessary (lines 159–178). `Cardinal.mk_le_of_injective`, followed by `Cardinal.mk_fin`, gives `4 <= componentCard S` (line 180). Using `Cardinal` rather than `Nat.card` preserves the meaning when the quotient is infinite. The strict comparison `3 < 4 <= componentCard S` and specialization of the universal conjecture at the admissible three-dimensional box prove its full negation (lines 182–191).

## Boundary, holes, attribution, and scope

All eight `Challenge.lean` theorem signatures match the eight `Solution.lean` signatures after whitespace normalization; I checked this independently. `Solution.lean` imports only `NLA.IV06.Proof`, and that file imports the definitions and ordinary library/tactic modules, never Challenge. The deliberate `sorry` declarations are confined to the statement-only Challenge. No placeholder, custom axiom, unsafe declaration, implementation override, or local metaprogram creating proof declarations occurs in the actual definitions/implementation/exports. The root reviewer's authenticated transitive-axiom and kernel checks remain the evidence for the compiled import environment.

The formal exports establish at least four components and the negative answer to the universal conjecture. They do not assert exactly four components, all endpoints, a replacement general bound, or the source manuscript's optional full determinant-range surjectivity statement. This scope is adequate and accurately disclosed. Colbrook retains mathematical authorship; Stepaniants is credited for AI-assisted formalization; Hladík, Daney, and Tsigaridas retain original-question/background credit.

No checkout files were changed and no CI or Lean build was rerun.
