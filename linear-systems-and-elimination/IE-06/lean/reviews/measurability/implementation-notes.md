# IE-06 all-path event measurability

Date: 2026-10-06. Implementing agent: mathematical-review agent, now assigned
the measurability proof after the user expanded the task to require a complete
probabilistic proof. This is an implementation note, not an independent review
of its author's own code.

Before implementation, the coordinator independently approved these exact
statements in the team exchange: measurability of matrix coordinates, a fixed
Schur step, every stage of every fixed finite path, actual growth along a fixed
path, the admissible-path set, the matrix determinant, and

```lean
theorem exceedanceEvent_measurable_proved (n : ℕ) (t : ℝ) :
    MeasurableSet (exceedanceEvent n t)
```

The final source is `NLA/IE06/Measurability.lean`, SHA-256
`8bc5c37b83630e26e1d2e64c86971aee23c9640e384796ea929223ebed535592`.
No definitions or Challenge signatures were changed. Generic coordinate,
finite-maximum and Schur arguments are adapted from IE-04's existing
measurability module, preserving its copyright and author attribution.

The proof takes these steps:

1. Every matrix coordinate is measurable in the actual nested product space.
   Total real division makes every fixed Schur update measurable everywhere;
   valid elimination still separately requires nonzero pivots.
2. Induction gives measurable trajectories for every fixed path and every
   stage. Finite suprema of nonnegative coordinate norms and total division by
   the original entry maximum give measurability of actual path growth.
3. Admissibility is a finite intersection of nonzero pivot conditions and
   non-strict comparisons of absolute values of measurable trajectory entries.
   It includes every admissible magnitude tie.
4. The determinant is measurable by its finite permutation-sum formula.
5. The actual bad event is the nonsingular guard intersected with the union
   over the finite type of all path maps of admissibility and strict growth
   exceedance. No measurable pivot-selection function or assumed event
   measurability is used. The zero-dimensional guard yields the empty event.

The pinned Lean 4.33.1 development compilation succeeded. Eleven declarations,
including the private finite-supremum helper, have explicit kernel-trust
assertions and printed axiom audits. Every printed list contains only
`propext`, `Classical.choice`, and `Quot.sound`. There are no placeholder proofs,
new axioms, or native-decision tactics in the module. The successful log and
receipt are retained alongside this note; temporary compiled outputs were
removed. As documented in the receipt, the development compilation trusts the
existing pinned dependency cache and is not authoritative Linux replay.

This completes the exact event-measurability obligation. It does not itself
establish the growth-factor tail estimate or the full IE-06 probability limit.
