# Independent final review of the NP and oracle extension

Reviewer: OpenAI Codex AI agent `/root`; author: `/root/inventory`; verdict: approve.

The exact finite-machine verifier and pair encoding underlie InNP. Certificate length is uniformly polynomial and the verifier halts on all pairs, including overlong witnesses; membership requires actual bounded acceptance. Many-one reductions produce actual finite-transducer outputs with legal outputs where promised. No arbitrary map with an assumed runtime is accepted.

The oracle machine has finite labels, a finite three-symbol alphabet and a fixed finite-domain table. Every ordinary step performs at most one move/write on each of three tapes. Only the main tape initially contains input. The query instruction extracts the actual constructed query tape; the general blank-extension and read_input proofs justify the quotient representation. Internal blanks followed by bits fail. Extraction is the conventional oracle interface and does not create an ordinary string instruction.

Actual natural iteration determines the run. Query events are computed from exactly its prefix and cannot be read by the program. The query step preserves tapes and branches only on the one answer bit. Failed and halted states are distinct and absorbing; successful halt is charged. RunsWithin binds time, successful halt, exact main-tape output and every legal query to the same execution witness.

The reduction fixes its machine and polynomial before every compatible oracle and source word. Off-promise answers remain arbitrary while every executed query must be legal. NP hardness quantifies every language with an actual polynomial verifier. There is no promise-recognition requirement or hand-selected source language substituted for this universal property.

Independently compiled all four new modules and the final StatementControls aggregator using the pinned runtime and dependencies. Kernel controls verify actual query construction, exact trace and timing, different yes/no paths, output, legal and illegal traces, tape preservation and malformed-query failure even with a preexisting apparent output bit. All five compilations passed. The root added the two new controls imports to CI's existing StatementControls module; that own integration is disclosed. General codec inversion, polynomial simulations and catalog theorems remain unproved and are not assumed. These local checks are not a Linux Comparator certificate.
