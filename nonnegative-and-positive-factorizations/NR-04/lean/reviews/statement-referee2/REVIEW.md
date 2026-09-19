# NR-04 independent statement review — provisional, changes required

Reviewer: `/root/nr04_statement_referee`, an independent OpenAI Codex agent.
Phase: statement-only review, 19 September 2026 (UTC).
The reviewer did not author or modify the proposed packet and ran no Lean
compiler, proof implementation, Comparator, or publishing command.

**Verdict: REQUEST CHANGES / NO STATEMENT APPROVAL on these bytes.**
The intended mathematical boundary passes my adversarial semantic inspection,
but its first actual elaboration fails and the YAML is syntactically invalid.
The required two-approval gate must remain open. Corrected sources and the
successful exact-source header result require a scoped review continuation.

## Exact boundary reviewed

Packet: `.local-recovery-20260918/development/NR04-statements`.

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `628bbf8c2ef920ce2a170860819c7ad7a14b1fb309f252ddce59dd9855e4707f` |
| `NLA/NR04/Definitions.lean` | `ee6c60efb4385f6073acfb215a2be65ca3ea597e3e8b070eb25645d50714b036` |
| `NUMERICAL_TARGETS.md` | `5a758137ec0e9350283e66b5462ca12cf3f2fde1cd58b92ed88b1d668a0aa3cd` |
| `comparator.json` | `23fffe05b309033b5d7bd9cfad8b6ff9551433a4bd6fb92564b763e67c282e8b` |
| `formalization.yaml` | `ef115e9a93fb1bb413faee5d71d7cf80c239d7475bce13b992ec7e6303132bec` |

`AUDIT.json` records every packet-file hash and independently checks all 17
bound Git sources against the author's stated lengths and SHA-256 values.
I read the complete canonical README and authored manuscript at published
commit `71563f17926cd826a892c2bba0e294894ee57a5c`, including the geometric
arguments and explicit upper certificate, and the complete prior mathematical
review. Their hashes are, respectively,
`84db16a9536cf346475b1c62a2836de04c0d405b6d088593558963e04f7d5f6b`,
`45b562126348a7b51ce6bb50ff3230b041e3160c8d044a103f94656ec4bc64a2`,
and `e87593938732175b9188bdf9bb8c761dc086cc8fa6b9ba298942c5bed5775f80`.
The complete manuscript's hash is distinct from the separately bound reviewed
body. The old review is corroborating evidence, not approval of these headers.

I read the campaign review protocol and retained Tau Ceti reviewing guidance
and correctness, generality, reuse, and attribution rubrics at the documented
`afb424eda89e8ac96d9eb69f6a88972055a4cd1b` revision. This is an adaptation of
those review angles, not a run or endorsement of the official review service.
I also read the retained Comparator README and formalization.yaml v0.4 README
and schema. Pinned Mathlib inspection checked the actual rank, extreme-point,
least-element, convex-hull, affine-span, and cardinality definitions and
relevant rank/convex-hull API. This is a bounded search, not an exhaustive
claim that no reusable polytope theorem exists.

## Findings requiring correction

**F01 — blocking: real-number imports and implicit variables.**
`Definitions.lean` imports abstract matrix/convex geometry modules but no real
number module. Root's actual `recovery-028` compiler result fails on these
exact bytes with missing `LE ℝ`, `OfNat ℝ 0`, matrix multiplication, real
coercions, and ring instances. With automatic implicit variables enabled, the
unresolved identifier can be treated as an implicit type parameter instead
of the intended real field. The printed signatures therefore cannot be
accepted merely because they visually contain the symbol `ℝ`.

Add an explicit real import such as `Mathlib.Data.Real.Basic` and set
`autoImplicit false` in both Definitions and Challenge. Re-elaborate the
complete header closure serially. Review the amended bytes and actual
successful result before freezing. This preserves the intended mathematics
and catches future identifier omissions; no mathematical premise should be
added to repair the errors.

I inspected root's actual Definitions log and corresponding receipt. The
receipt records source hash `ee6c60...`, exit code 1, and a blocked
`NR04Challenge`. The log hash is
`a7589f66621f0bbb2bca9d03cf558f769a243f0244f359ac14a22d85b0d76f58`.
The full command, limits, timestamps, and receipt hash are bound in
`AUDIT.json`. I did not execute or repeat that Lean run.

**F02 — required metadata repair: invalid YAML scalar.**
At `formalization.yaml:105`, the unquoted value of
`verification.numerical_certificate` contains `(8 : Real)`. The colon followed
by whitespace is invalid in this plain scalar. My actual Ruby/Psych
`YAML.safe_load` call fails with `mapping values are not allowed in this
context at line 105 column 80`. Quote the entire value or use a folded block.
The exact command, exit code, stdout, and stderr are retained. YAML schema
validation has not succeeded: the parser fails before schema validation.

As a routine status update after repair, the live metadata should distinguish
the failed first elaboration and any later successful header run from an
unrun proof or Comparator. Preserve the numerical-first record as historical
evidence; do not retrospectively claim an earlier success.

## Contract-by-contract semantic inspection

These judgments concern the intended mathematical content, subject to F01.

| Contracts | Inspection and result |
| --- | --- |
| C01 | Exactly `0 < (8 : Real)`. This is a deliberately minimized numerical obligation, not the problem's proof. Its future kernel-mode LeanCert proof must actually be consumed to establish the nonzero minor in C06. The signature alone does not enforce that consumption. |
| C02 | Adding one to both zero-based real indices leaves the difference unchanged. `Fin 9` covers precisely the nine canonical points; no modular or cyclic arithmetic occurs. |
| C03 | `Int.natAbs` of the integer centered label ranges from zero through four. Its real coercion is the absolute centered coordinate. The center and both endpoints remain present. |
| C04 | The stated reflection identity is valid for all real signs, including zero, equality, and opposite signs. There is no finite-test or positive-only restriction. |
| C05 | The actual 9-by-7 and 7-by-9 matrices have the source's five label selectors and two reflected sign terms. Their full product, and both nonnegativity predicates, are requested. |
| C06 | `Fin.castAdd 6` selects indices zero, one, and two without wraparound. Their determinant is eight. `Matrix.rank` is actual finite-dimensional image rank, not a user-defined proxy. Rank equality three needs both the minor lower bound and exact rank-at-most-three decomposition. |
| C07 | Every diagonal entry is zero; each pair of distinct indices has a strictly positive squared difference. All off-diagonal cases are retained. |
| C08 | The section is the actual convex hull of all columns of U intersected with the actual affine span of X. Both stochasticity predicates include nonnegativity. Rank X three forces a two-dimensional affine span; rank U at most four forces hull dimension at most three. The number of generators is at most six, not an assumption about the number of section vertices. Actual extreme points are counted, and finiteness is explicitly required. |
| C09 | The number and rank of U's normalized generators are unrestricted. Positive off-diagonal entries and one zero per column supply distinct facet-interior contacts in the two-dimensional orthant section. The conclusion asks for actual finite extreme points and a lower bound N. No polygon-contact lemma, chosen normal fan, or bound on the vertices is supplied as a premise. |
| C10 | Arbitrary nonnegative real W and H are allowed, including zero columns and every width at most six. Normalization and deletion of zero columns are consequences the proof must establish. They are not assumptions on the canonical factors. |
| C11 | For all rectangular real factors and every width at most six, rank of the product three entails one factor has rank at most four. Both ranks at least five would violate Sylvester: product rank is at least 5+5-6=4. No nonnegativity is needed or assumed here. |
| C12 | The source's general lower bound includes nonsymmetric matrices of every order at least nine and all natural widths at most six. An explicit nonnegative-M premise is unnecessary because zero diagonal and strictly positive off-diagonal entries already imply it. Transposing preserves all these properties. |
| C13 | The actual canonical matrix excludes every width zero through six. There is no rational-only factor restriction and no assumption that either factor has the product's rank. |
| C14 | Mathlib `IsLeast` includes both membership of seven in the feasible-width set and a lower bound against every feasible natural width. It cannot default to seven if no factorization exists. |
| C15 | The original width-six question is stated with both arbitrary real factor matrices explicit, all entries nonnegative, and exact matrix equality. It is a complete negative answer, not only a restricted nonnegative-rank result. |

## Adversarial geometry and boundary checks

C08's dimension split is legitimate only after showing nonempty normalized
column sets and the rank-minus-one affine dimension formula. Rank X three and
containment rule out dimensions zero and one for the outer hull. When the
hull has affine dimension two, its affine span equals the plane and the
section is the whole hull, with at most six vertices. In dimension three,
the manuscript uses the genuine facet bound `f <= 2v-4` for a 3-polytope with
`v <= 6`. Restriction to the plane gives at most eight nonredundant halfplanes
and hence eight edges/vertices. Repeated/nonextreme generators, nonsimplicial
facets, and planes through a vertex, edge, or entire facet are not excluded.
All these prerequisites remain proofs to implement; the headers neither
prove them nor smuggle them in through a custom structure.

For C09, every point in the affine span of normalized X has coordinate sum
one, so its nonnegative-orthant section is bounded. Rank three makes that
section two-dimensional. At column j, exactly the j-th inequality is active;
the others are strict and the j-th coordinate is nonconstant on the plane.
This is a contact in the relative interior of a genuine edge. Distinct
indices cannot describe the same edge, because the corresponding other
column has positive j-th coordinate. The normal-fan argument must handle
edge-exposing directions by the half-open assignment or an equivalent exact
argument; unique maximizers cannot be silently assumed. I found no excluded
degenerate case in the stated domain.

The geometric hypotheses are not inherently inconsistent: normalized
3-by-3 off-diagonal-one/diagonal-zero X and U equal to the 3-by-3 identity
provide a nontrivial common example for C08/C09. The real-factor predicates
have the explicit seven-term canonical witness. C12's width bound is a
conclusion, not embedded into any input structure. For k=0 or very small N,
rank hypotheses become impossible in the correct mathematical way; the
unconditional final canonical statements retain every smaller width.

## Checks actually performed and limitations

The independent `audit.py` uses only Python standard-library exact integers
and fractions for its finite arithmetic. It checked all 81 entries of the
seven-term product, nonnegative factor entries, determinant eight, and ranks
`rank D=3`, `rank W=6`, `rank H=4`. It did not import or execute the source's
checker. This diagnostic supports the data transcription only; it supplies
neither the general geometric lower bound nor a Lean proof.

The same audit checked all 15 Comparator names in order against the headers,
exactly 15 intentional Challenge placeholders, no definition holes, an absent
Solution, and only `propext`, `Classical.choice`, `Quot.sound` as permitted
axioms. Actual Comparator checking and its non-root Linux sandbox remain
unrun. Header elaboration is root's separate failed run, as documented above.

Attribution distinguishes Matthew J. Colbrook's mathematics and Cambridge
affiliation from George Stepaniants's Caltech Computing and Mathematical
Sciences formalization contribution, and retains the earlier reflection
upper-bound attribution. No new mathematical discovery is claimed and no
George Stepaniants email appears in the packet. The metadata honestly
describes an incomplete proposed formalization, subject to the parse repair
and current-status update.

The required next gate is correction and exact-source header re-elaboration,
followed by both independent approvals. There is no proof approval, no
canonical Lean-verification completion, and no count increase from this
report. Substantial polygon/polytope work remains even after the statement
gate passes.
