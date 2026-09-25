# MD-06 Lean work area

This folder does not edit the manuscript. `Definitions.lean` provides a semantic interface for the exact target. `Challenge.lean` states both source conclusions independently of any proof. `Solution.lean` contains only an axiom-free projection from the strong event to its nonsynchronized critical point.

The full theorem is deliberately marked unverified in `formalization.yaml`. The shared workspace now contains the pinned Mathlib cache, and the files have been rerun with it on `LEAN_PATH`; LeanCert and Lean Comparator remain unavailable, and network access cannot fetch them. Even with those dependencies, the source proof needs random regular graph asymptotics, torus calculus, and a quantitative correction argument.

