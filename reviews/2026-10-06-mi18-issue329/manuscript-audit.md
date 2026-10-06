# Independent manuscript and certificate-checker audit

Date: 2026-10-06. Reviewer: Codex AI agent `statement_audit`, separate from the agent that wrote the manuscript and checker. Scope: conventional mathematical argument, exact certificate, Python verifier, and correspondence of the proposed canonical README and resolution notice. This is an AI-agent review, not human peer review.

**Verdict: approve.** No substantive mathematical or certificate-verification defect was found. The manuscript gives a complete computer-assisted disproof of the unchanged MI-18 target, with an exact finite arithmetic step. Its positive-definite perturbation and comparison point are explicitly existential.

## Reviewed files

The reviewed files are in `matrix-inequalities-and-norms/MI-18/` in this change. SHA-256 at review:

| File | SHA-256 |
| --- | --- |
| `solution.md` | `662d818cc493ac8ebb57bc7b6b80afc82f7e6b630ac5a5a68f375f7a15fb1c90` |
| `verify_certificate.py` | `00f06921a745efaad79c1cca847b72b1e8fc9f86d63e4294d7583914bfc00d8b` |
| `certificate.json` | `dc0e3ce61bd455b5904752a0d4781d8500e0f510e51f36343f6275aa433a504b` |
| `README.md` | `373154ed3f111572f9d3f0a345c3504ffe935a208714ede6ce9ed75a799ba563` |
| `../../RESOLVED.md` | `1097a24e5af60579de604a6074eb919e957796cf402186d195787d2605d74350` |

The source comparison uses external revision `4200da4fc1a132d69c23fb877795b5b72089544b` of `KitaKen1/bapat-lal-q-permanent-lean`, especially `lean/Bapat/Certificate.lean`. Source-review approval of the formal theorem's correspondence is recorded separately in `statement-audit.md`.

## Mathematical review

1. **Reality and fixed ordering.** Section 1 correctly pairs a permutation with its inverse under complex conjugation. The inversion-pair bijection is explicit and preserves the inversion number. The zero-based indices are an order-preserving relabelling of the canonical one-based indices.
2. **Endpoint identity.** Lemma 1 separates ascents and descents for each ordered pair of rows, with the complementary permanent summing every bijection of the remaining row and column sets once. The identity is `2D(A) = binom(n,2) per(A) - T(A)`; its factor 2, minus sign, and use of increasing orders in both two-element sets are correct. It holds without positivity assumptions and with complex entries.
3. **Mixed Gram permanent.** Lemma 2 groups coordinate choices into a row subset and a column subset of the same size. The multiplicity is exactly `k!(m-k)!`; the column coefficient is conjugated. The argument also covers the empty complementary matrix when n = 2.
4. **Wedge norm.** For row pairs I,J, `det H[I,J] = w_I conjugate(w_J)` has the correct conjugation. Combining this with the mixed complementary permanent gives the squared norm of the *sum* of wedge polynomials. All cross terms occur; the manuscript does not accidentally substitute a sum of individual squared norms.
5. **Sign and degree.** A fixed marked factor receives j positive and n−1−j negative contributions in the pair sum, giving coefficient 2j−n+1. Thus F = −g for the stated weight n−1−2j. The degree bound for F is n−2 directly from its definition, so the degree-n−1 term in g vanishes without division or nonzero-coordinate assumptions. The numerical checker additionally checks the cancellation exactly before omitting the final zero coefficient.
6. **Recurrences.** The marked-product recurrence uses the final n throughout, not the current prefix length. The independent wedge recurrence follows from adding pairs involving the new row: their sum is `j b_j p^(j) - l_j (p^(j))'`. Its implementation does not reuse the marked-factor weights. The two final coefficient lists are compared exactly, including the trailing zero.
7. **Arithmetic and sign.** The factorial norms, Gaussian multiplication, and squared moduli are correct. The exact lower bound S > 10300P and 10296 = binom(144,2) give `2D(H) < -4P < 0`. Decimal division is used only to report approximate orientation values; it is absent from all acceptance conditions.
8. **Admissibility and strict decrease.** The displayed VV* construction proves PSD. All printed first coordinates are nonzero, giving positive diagonal and P > 0. The calculation H[0,1] = 9795−1288i is correct. Positive ε gives positive definiteness and leaves this entry unchanged. D(H+εI) is a polynomial in ε, so negativity persists for some positive ε. A negative derivative at q = 1 implies `P(1-h) > P(1)` for sufficiently small positive h; choosing h < 1 gives the manuscript's stronger q₁ in (0,1), q₂ = 1 conclusion. This stronger localization is justified by the prose argument even though the cited external existence theorem does not specify q₂ = 1.

No circular use of the claimed disproof, unproved rank-two identity, implicit real-symmetric restriction, or unjustified explicit perturbation was found.

## Executed checks

I ran `python3 matrix-inequalities-and-norms/MI-18/verify_certificate.py` successfully. I also ran a separate review script using the Python standard library that:

- Parsed the complete ordered row list from the pinned Lean source and compared all 144 triples against `certificate.json`.
- Parsed all three indexed blocks of the manuscript table, verified that indices 0 through 143 occurred exactly once, and compared each triple to the JSON and pinned source.
- Independently recomputed the marked-product coefficient recurrence and checked both integers against the full decimal `expectedP` and `expectedS` constants in the pinned Lean source.
- Enumerated every permutation for the first 2, 3, 4, and 5 source rows. Direct Gaussian-integer evaluation of the permanent and inversion-weighted endpoint derivative agreed with the coefficient formulas, including the factor 2 and sign. These are supplementary consistency checks, not a substitute for the general proof above.
- Confirmed rejection of five corrupted certificate files: a changed coordinate, a transposition of the first two rows, a removed row, a boolean in place of an integer, and false row-digest metadata.

The canonical ordered-row digest was
`213d6aacc5262c80ca8f27ae598b3205ad759a23422eab5fd79ea73ff98aa550`.
The recomputed integers had 768 and 772 decimal digits. Their decimal-string SHA-256 values were:

- P: `a5be63619a86ea1fbd54987f59cbc599b00ae2dc16bb6c97ab12873c91209ffe`.
- S: `26508b5a6bf2ebb5c453892e7deed4cb086dcdd38116fe9a6f747f5b3bc7bb1e`.

All arithmetic checks passed. The fixed ordered-row digest appropriately makes this a verifier of the published certificate, rather than a search tool accepting arbitrary replacement witnesses. A changed coordinate or row order is rejected before arithmetic, and the full source comparison independently establishes what the accepted digest represents. Type checking uses `type(x) is int`, so JSON booleans cannot masquerade as integer coordinates.

## Canonical status and documentation

The proposed canonical README and MI-18 resolution entry retain the original question, ID and path; retain the prior order-four result; and correctly replace the stale claim that the arbitrary-order assertion remains open. They describe the order-144 result as a negative resolution, distinguish the existential perturbation from unverified particular numerical choices, and state that the catalog reviewed the external public Lean record without rerunning Lean locally.

The manuscript credits the supplied certificate and formalization to Kitamura, discloses that Codex prepared the exposition/checker, and makes no claim of Kitamura's approval, human authorship of the exposition, external human peer review, or discovery priority. No additional mathematical correction was requested. A separate presentational note about adapting the manuscript's Markdown math delimiters to repository GitHub conventions was sent to the author and maintainer; it does not affect this mathematical approval.

## Limits

This review does not determine the least counterexample order, provide a real-symmetric counterexample, or certify a fixed perturbation such as 10^70 H+I. It did not run Lean, formally verify Python, or visually inspect the generated PDF. The prose theorem and arithmetic were reviewed independently of the author's public formal-build report; PDF layout and the formal evidence gate are separate checks. Approval is specific to the reviewed bytes above; material mathematical or checker changes require another review.

## Final-byte equivalence addendum — 2026-10-06

The same independent reviewer inspected the final manuscript after three presentation/bibliography changes: the reproduction-command code fence lost its `text` language label, the table's separator widths were expanded for rendering, and the Bapat–Lal and Mitchell source references were added. Reversing precisely these three changes in memory reproduced the original reviewed manuscript SHA-256 `662d818cc493ac8ebb57bc7b6b80afc82f7e6b630ac5a5a68f375f7a15fb1c90` exactly. Thus every formula, proof paragraph, table datum, scope qualification and attribution paragraph is unchanged.

**The approval extends to the final `solution.md` SHA-256 `5bf56cfd29c97c0d7817d9ebbfe36c0afd9c8e68a39e6cfba331fb374f7aa72c`.** The verifier and certificate hashes remain exactly those recorded above. No new arithmetic execution was needed because their bytes and all mathematical content were unchanged.

The maintainer confirmed that ordinary mathematical Markdown follows the existing `solution.md`/`render_solutions` workflow; the canonical README separately uses the protected GitHub notation. The earlier formatting note is therefore resolved without mathematical changes. All review limitations above remain in force, including the absence of local Lean execution and PDF visual review by this reviewer.
