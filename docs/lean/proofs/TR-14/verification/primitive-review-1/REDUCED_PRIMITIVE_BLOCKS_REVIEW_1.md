# Independent review of ReducedPrimitiveBlocks.lean

Reviewer: OpenAI Codex AI agent `/root/solved_inventory`, 2026-10-18.
Decision: **PASS** for the exact primitive scalar-block support source, SHA-256 `d80c1acdfe8916ffcfdc7700bd441b701eb596fff4023502af7e42b9b23c96cd`.

I read the complete frozen source independently of author `/root/fr05_statement`. Its product equivalence is constructed, rather than supplied: actual Artinian maximal residue fields of the reduced finite-dimensional complex algebra are finite over ℂ, so the algebraically closed scalar map is bijective. Their product, reindexed by an actual `Fin t` equivalence, gives the promised complex algebra equivalence. The trivial/empty-spectrum case is included.

Given that actual equivalence for a subalgebra, each ambient primitive indicator is precisely the inclusion of the inverse image of a coordinate delta-one function. Nonzeroness, idempotence, pairwise zero products and sum equal to the ambient identity are transported through the injective algebra equivalence and ambient inclusion. The scalar action theorem uses the actual scalar coordinate of the supplied subalgebra element in that equivalence. It is not an assumed primitive-block action, a partition of nilpotent derivative coordinates, or a full ordinary lower bound.

Fresh independent isolated replay passed 4/4 source commands: shared Infrastructure, live TR14 statement, ReducedSubalgebras, and ReducedPrimitiveBlocks. Only pinned external dependency objects were reused; no shared NLA objects were loaded. The exact source snapshots, every command, source/log hashes and unchanged-current-source checks are in `primitive-independent-build.json`. Kernel assertions pass, and both printed theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

This review excludes independent approval of my own consumer modules. It does not prove the remaining block-context transport, unrestricted ordinary lower bound, unchanged TR-14 Target, or Linux/Comparator acceptance.
