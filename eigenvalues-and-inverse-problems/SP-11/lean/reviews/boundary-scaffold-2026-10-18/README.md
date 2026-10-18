# Historical pre-Solution package configuration

This exact lakefile.toml has SHA-256
`f00c89d3dd744b0436de0d5bdc41209af4574356c6a07da1e2f6588af66905b5`, the original hash in boundary-source-lock.json.
The current complete package adds Solution as a library and changes defaults from
Challenge/Identity to Solution/Identity. Challenge, copied statement definitions,
Identity and Comparator selection retain their original reviewed bytes.

To reproduce the earlier boundary-only source/configuration check in a temporary
copy, use this preserved lakefile.toml in place of the current one and omit
Solution.lean and the subsequently added proof module directory. The original
boundary build commands, outputs and actual source hashes are retained in
../boundary-root-evidence-2026-10-18 and ../boundary-review-1-evidence (the original
local author run is under docs/lean/proofs/SP-11/boundary-scaffold-evidence-2026-10-18).
That check is historical and establishes no target proof.

For the complete current package use verification/check_package.py and
proof-source-lock.json. A checker written for the original scaffold should read
this retained old configuration when checking the historical lakefile hash; it
must not require the finished package to have boundary-only defaults. Real
completed-project metadata and Linux verification remain separate gates.
