# TR-27 independent statement referee 1

Date: 2026-09-22. Reviewer: `/root`, Codex AI agent. Author of this TR-27 boundary: `/root/canonical_inventory`. I did not write the TR-27 definitions or statements and no TR-27 proof implementation existed during this review. I independently read the canonical problem, the complete Colbrook manuscript, all definitions and 25 Challenge signatures, numerical targets, configuration and dependency pins. This is AI-agent review, not human review or official Tau Ceti endorsement.

Verdict: **APPROVE the exact mathematical statement boundary below for proof implementation after the second independent approval.** This approves no mathematical result, runtime verification, publication or status promotion.

## Canonical fidelity and nonvacuity

`CanonicalConjecture` states the full implication with ordinary projective span rank, Zariski border rank and the actual tensor square, quantifying arbitrary complex vector spaces with finite coordinates and admissible projective varieties. A finite linear coordinate presentation is equivalent to a finite-dimensional ambient space; the explicit `finite_coordinates` and `coordinate_transport` obligations expose this convention. The universe convention does not omit a finite-dimensional mathematical example. In particular, the specific twelve-dimensional witness lies in the universal domain.

`Admissible` is a classical homogeneous-coordinate definition, not an arbitrary predicate named variety: it requires the actual polynomial ideal to be homogeneous and prime, the quotient ring reduced, a nonzero cone point, and full linear span of its entire complex zero locus. Over the algebraically closed field complex, a proper homogeneous prime ideal with a nonempty projective zero set describes a reduced irreducible projective variety. No smoothness, dimension-one assumption, rank equation, existence of a low-rank decomposition or desired conclusion is hidden in these conditions. The required `admissible_geometry` proves classical point-set closedness, the closed-set union criterion for irreducibility, and full projective span; prime-spectrum points are not silently substituted for complex projective points.

The rank-at-most definitions allow arbitrary complex coefficients, repeated points, and every finite length up to the bound. Projective ranks use Mathlib's actual projective subspace span. Natural-number infima cannot be trusted without nonempty upward-closed length sets, so the Challenge explicitly requires existence and minimum equivalences both for ordinary and Segre ranks. Border closure quantifies every homogeneous polynomial of every degree that vanishes on the whole rank locus. The affine closure is the actual all-polynomial vanishing ideal/zero-locus operation; the projective-affine bridge and representative-independence declarations must be proved. Empty rank-zero loci, the zero affine vector and arbitrary representative scalings are correctly exposed, rather than assumed away.

`segrePoints`, `IsTensorSquare` and `TensorRankAtMost` use the actual complex tensor product with independent left and right factors. A nonzero scalar relation to a projective representative defines the same projective point. The required tensor-representative, Segre-rank and Segre-minimum bridges rule out zero-tensor defaults, symmetric-decomposition restrictions and merged-mode substitutions.

## Exact witness and source comparison

The source space has 13 coordinates and the target has 12. `coordinateIndex` selects exactly 0,2,...,12. The exact scalar formula `S_j=1+2^j+3^j` and quotient `5w_j−S_jw_1` agree with the manuscript; the center's coordinate 1 is −5. All arithmetic is over complex numbers with exact natural casts. Finite parameters and infinity are both included. The homogeneous coordinate formula has degree 12; exponent subtraction is safe because every index is at most 12. The nonvanishing and image/cone equality assertions include the zero homogeneous input, zero output, arbitrary scalar multiples and infinity.

I independently expanded the new integral-route identity using `a=s^12`, `b=s^11t`, `H_0=5a−3b` and `aH_2=5b²−14ab`. The a², ab and b² coefficients each cancel in `85a²+(8H_0+9H_2)a−5H_0²`. Label 2 corresponds to Lean coordinate 1; no off-by-one error occurs. This is a transparent auxiliary algebraic route, with unconditional integrality and equality of the **whole** zero locus to the whole parameter image required separately. Merely proving inclusion in an algebraic closure will not satisfy the frozen target.

The three explicit parameter values 1,2,3, tangent vector, polynomial degeneration with first coordinate −3, independence cutoff eight, rank three, border upper bound two and square rank nine match the original counterexample. The lower bound is against arbitrary complex decompositions on the entire curve, including repeated points and different factors. Rank three with border rank at most two and square rank nine refutes the precise original implication. The source's stronger smoothness, exact border rank two, prescribed longer delays and eventual saving are not necessary for this negative answer and are honestly omitted. Original proof credit remains Colbrook; the formalizer's requested name and Caltech affiliation are separate, with no contact email added.

## Mechanical and packaging checks

I independently rebuilt Definitions and Challenge with Lean 4.33.1 in fresh output directory `/private/tmp/nla-tr27-root-statement-build`; the retained root log records both exit zero and exactly the 25 deliberate Challenge-placeholder warnings. Existing pinned package caches were used. This is development typechecking, not kernel verification of the placeholders, fresh dependency authentication or Linux Comparator.

The Comparator configuration selects all 25 advertised obligations, no definition holes, and only the three standard permitted axioms. No Solution imports or proof bodies exist yet. I requested a packaging correction from invalid metadata role `statement-draft` to the schema's `substantive-development`; incomplete status and empty `main_results` remain explicit. The author corrected it and recorded schema validation. This correction changes no mathematical bytes. I have not claimed that the completed-project validator should accept this unfinished draft.

The remaining work is substantial proof implementation and independent final review, including genuine closed-image equality, irreducibility, all-point rank bounds and every semantic bridge. A finite coordinate check or acceptance of this Challenge alone permits no Lean-verified promotion.

## Exact byte binding

- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `NUMERICAL_TARGETS.md`: `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52`
- `comparator.json`: `2cf6d47dd9b3ad53fabd80b87c49476eefebd07c930994929a8534a0d8b46291`
- `formalization.yaml`: `01506a7002e2e0eff6404e8354a5317c7f44cc940f638c45d03a1077a7dbdb80`
- `reviews/root-statement-typecheck.log`: `d6d74c9df7c3081fad167fe3b1d5f8b39278461e202d473060679839df43e794`
- `lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `lakefile.toml`: `6414104fc28d3d7a3b2f6960d897a2509f28a4f3fca4d182c087e27c0c472120`
- `lake-manifest.json`: `dc5d5e3067aaa5b8e5fa140ba328adaf525a8c31a4968108db28724475a78df6`
