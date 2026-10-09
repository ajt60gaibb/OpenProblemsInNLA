# Native build: generated-output disk limit

The 30 September 2026 run against source commit
`ac582d01532a914538cbfb74863437b18433038a` used native storage for both Lean
and Mathlib. The earlier shared-filesystem read failures did not recur, and
the Solution build progressed substantially. It nevertheless exhausted disk
space while writing generated build outputs. The [actual log](comparator.log)
records the failure; this attempt did not verify MF-17.

The next fresh run starts with an empty project `.lake/build/ir` directory
backed by the larger volume. This stores generated C/setup files, while all
imported Lean libraries and compiled proof objects remain native. No prior
project build output is reused. Standard OS stop/resume signals limit active
Lean compiler processes to two. The checker, sandbox, target statements,
proof sources and axiom policy are unchanged.
