# SP-11 Lean boundary scaffold

This package freezes the exact unrestricted real symmetric delta conjecture for
all finite simple graphs with at least one vertex. It contains no completed target
proof. `Solution.lean` is deliberately absent while the shared proof is completed.
`Challenge.lean` contains the single deliberate Comparator placeholder.

The live statement, statement-checking infrastructure, separately frozen reviewed
statement, original canonical page and numerical specification are copied byte for
byte from the shared reviewed sources. `Identity.lean` proves definitional equality
of the two Target propositions; it does not prove Target. The numerical
specification's preimplementation wording records its historical freeze phase.
The original ID, canonical page, target, status, attribution and published artifacts
are unchanged.

The pinned dependencies are Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. `lake build Challenge Identity`
checks this statement boundary after materializing those dependencies. The default
build is a boundary check, not verification of a solution. Build products and
materialized dependencies must not be committed.

`comparator.json` already selects the future exact export `NLA.SP11.target` from
`Solution`. Metadata advertises zero completed main results. Consequently the
repository's completed-project manifest/Comparator validation is expected to fail
until the full proof, Solution wrapper and final metadata are added. Do not weaken
that validation or treat a boundary build as acceptance.

Two independent reviews of this frozen package boundary are required before
writing Solution. The package source lock records this boundary's actual bytes;
that review lock is not an extra automated verification profile. The final
package needs the closed proof source imports, fresh independent kernel/scope
reviews, and the repository's real isolated Linux Comparator plus LeanCert
verification before any canonical status promotion.
