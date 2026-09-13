# RA-09 scalar helper completion

**Complete, frozen helper for contracts 8–10; local validation only.** Authoring agent: `/root/formal_review_standards`. This agent previously supplied statement referee 2 and is consequently ineligible as an independent final mathematical referee. The accepted proof gate and implementation-role records are preserved unchanged.

`NLA/RA09/Scalar.lean` SHA256 **be27edbd0f42e83fb825095bae65c48c8d90e8d1614ed90871abace1f55b6f17**, 10,354 bytes, provides exactly:

- `NLA.RA09.admissible_scalar_consequences_proved`;
- `NLA.RA09.scalar_branch_certificates_proved`;
- `NLA.RA09.ordered_scalar_certificate_proved`.

All three have the complete frozen Challenge types, checked against the actual elaborated reference declarations by [Inspect.lean](Inspect.lean). That inspection imports Challenge only to inspect reference types. The implementation itself imports Definitions and actual library/tactic/trust modules; no Challenge theorem enters its proof closure.

The proof starts from genuine concavity between zero and a positive argument, retaining the nonnegative `f(0)` contribution. A cross-multiplied inequality yields all ratio, threshold, Lipschitz and vanishing consequences, including zero `f(tau)`. The explicit unbounded SOS proves the first branch quadratic positive, and all three exact rational factors are proved with their endpoints. The full certificate uses the squared Lipschitz bound when `b≥tau`. Below tau, positive normalization yields the two scalar lower bounds and the proved branch certificate; the same positive square rescales the entire inequality, including its positive part.

The normalized third branch is slightly simpler than the manuscript presentation: for `z≥d` and `v≥d`, split `v≤z` versus `z≤v`. In the first case `(z−v)(z+v−2d)≥0`; in the second, `2dv≥2dz`. Together with the positive part this proves the required bound without a further threshold split. This changes no frozen statement and introduces no new assumption.

Only exact real algebra and actual concavity are used. There is no interval subdivision, sampled replacement of an unbounded variable, artificial numerical singleton, `native_decide`, custom axiom, `sorry` or admission. LeanCert supplies explicit kernel trust audits on all five substantive scalar declarations. Mathematical credit remains Matthew J. Colbrook, Sections 2–3 of the retained Frobenius-transfer manuscript. George Stepaniants receives AI-assisted formalization credit with the Department of Computing and Mathematical Sciences, California Institute of Technology, without a contact email.

The final check [final-4qsv7b4x/result.json](final-4qsv7b4x/result.json) used the same owned private prefix after removing its prior generated project objects, with exact MI-22 dependencies read-only. Fresh Definitions, Scalar, Challenge and inspector commands all exited zero in **13.78 s, 5.89 s, 3.52 s and 4.64 s**. Scalar and inspection had no warnings; only Challenge's 17 intentional reference warnings occurred. All **eight kernel/standard-three reports** passed. Actual dependency traversal audited **10 reachable project declarations**, retained seven named material dependencies including genuine `ConcaveOn`, and retained both private scalar helpers. Every traversed declaration had permitted transitive axioms, with no unsafe, partial or bodyless proof. The inspector rejected any use of the three reference Challenge theorems.

All **31 frozen project inputs and 17 original fixed-base Git source/policy files** remained byte-identical, and all ten exact dependency pins were clean before and after the final run. No dependency cache was copied, downloaded, rebuilt or modified. Four earlier development attempts remain with their original source snapshots and raw logs, including two failed elaborations and two successful intermediate compilations; an intermediate successful compile still had redundant-tactic warnings. The final source removes those redundant tactics and passes the stricter fresh check. No failed attempt is represented as a passing proof.

This is a contributor's helper handoff, not an independent final review or an authoritative Linux check. Full matrix integration, all 17 exports, two eligible independent final referees, actual Linux Comparator/default-kernel/control verification and publication review remain required. No canonical status, frozen mathematical statement, pin, original source, commit or push was changed.
