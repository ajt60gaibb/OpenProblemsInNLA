# TR-26 independent isotropic-endpoint review

**APPROVE the literal isotropic endpoint at immutable checkpoint 4692336f0e1a50d5e261bba68277875da30fba51. No source correction required.**

Reviewer: non-author AI agent /root/verification, 2026-10-26. This approves exactly the original isotropic reduced-degree conjunct for every d≥2. It does not approve a nonisotropic endpoint, full Target, proof-status promotion, Linux run or Comparator acceptance. The canonical status remains Solved.

The actual theorem is:

    theorem NLA.Proofs.TR26.isotropic_degree (d : ℕ) (hd : 2 ≤ d) :
      NLA.Statements.TR26.HasReducedDegree d (2*d)
        (NLA.Statements.TR26.IsotropicImage d)

There are no extra chart, pivot, genericity, polynomial-certificate, matrix or geometric hypotheses on this endpoint.

## Immutable inputs and mechanical evidence

The 33 sources match ISOTROPIC_ENDPOINT_CHECKPOINT.json exactly (SHA-256 310cdbff42c1303419de04ff882ab549d8163cf26ccb7b58a4beb5e528530ba4). The prior 27 support sources are byte-identical to reviewed 57f8dcdb. I read all six added files completely and checked their use of the previously reviewed definitions and helpers.

| Added module | SHA-256 |
| --- | --- |
| WronskianLinear | 4d713bb5b34b0a815d505527974a049b6e72937e85a7b1e9123c1f2b2ee4b043 |
| WronskianCharts | 24b5849ab3f79b47395118f1e5a2920d4c8b3ff26996bffdee554c124767daa5 |
| CriticalEquation | 09804e70dc838099a5763fc4feef39d32b72c043fc187ccd131318ac0e7ecb34 |
| IsotropicChartCover | dc34518a77b10176309949a1ec6be33e307c10bd455d2574b5c5fbe74eaf8eb4 |
| IsotropicImageContainment | 570901446217c11b4f9f659cb664921f0794aa76bf58a12823ab61f031214933 |
| IsotropicDegree | 507bbb439ed82d0c87144de91a8f76d611ddb14bbd24d504a9544b351474fd25 |

The independent replay passes **88/88 checks and all 41 expected compiler outcomes**. It compiles all 33 proof/support modules, Infrastructure, live TR26 and Reviewed.TR26 from immutable Git objects into a newly created private directory: **36 source modules**, with no author project objects reused. All **288 explicit declarations** pass actual kind, kernel-trust and transitive axiom checks: **219 theorems and 69 definitions/abbreviations**.

The endpoint is an actual theorem and has exactly propext, Classical.choice and Quot.sound in its axiom closure. Every audited declaration uses a subset of those three; no support source contains a hole, custom axiom, native_decide, unsafe implementation or external attribute. All ten dependency checkouts match their original manifest revisions and remain tracked-clean before and after replay.

The compiler is Lean 4.33.1, arm64 macOS, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Mathlib is 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert is 621a43d7cf21f87872392a01e874f2f1dbddc926. Existing pinned dependency objects are read; dependencies are not rebuilt.

The exact consumer is generated from the preapproved Challenge isotropic header and accepts the actual theorem. Literal live/Reviewed Target identity holds by rfl. The actual nonisotropic_degree and target exports remain absent from this source environment. Separate real controls reject all three original reference placeholders through sorryAx, a proof-valued definition presented as a theorem, and a theorem depending on a fresh custom axiom.

All **24 original inputs** equal their locked hashes/lengths, frozen packet copies, published base 5487945e5a72abd952b0c89915915de8cc9b3e65 and this checkpoint. The preapproved lock is unchanged at 59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c. Thus the full original target, 217 permanent ID/path entries, canonical README, manuscript, specification and Reviewed definitions are preserved. Both retained author-receipt collections match all 33 source hashes and exit-zero records; those author builds are distinguished from this independent replay.

The separately computed actual endpoint import closure has **34 own modules: 32 proof modules plus live statement and Infrastructure**. The fresh replay additionally compiles CurveNormalRank and the Reviewed boundary. External imports are only the pinned Lean runtime, LeanCert and Mathlib modules. ENDPOINT_IMPORT_CLOSURE.json records exact hashes and edges.

## Mathematical assessment

WronskianLinear constructs the actual linear Wronskian map with the correct N′D−ND′ orientation. At every affine t the critical functional is nonzero: at a denominator root, the actual numerator 1 uses D′(t)≠0; away from a denominator root, the actual numerator X−t gives the nonzero value D(t). Both numerators are supplied by genuine numerator surjectivity. Expansion in the independent symmetric-coordinate basis therefore produces an actual nonzero coefficient pivot, without a genericity assumption.

WronskianCharts identifies that coefficient family with the concrete Wronskian and discharges every generic chart premise needed for the affine incidence and ramification implications. It uses the actual nonzero denominator polynomial, exact quotient-criticality identities, genuine chart derivatives and independent radial/tangent vectors. The analytic argument still quantifies over the original full vanishing ideal. Continuity fills denominator-root omissions while nonzero H and pivot persist locally; at a double root the matrix velocity is zero. No selected finite ideal or unproved localized-ideal equality is substituted.

CriticalEquation inserts the **universal parameter-coefficient** binary Wronskian into the incidence ring; H is not frozen at a test matrix. Homogeneous scaling proves that this is a polynomial of the actual full vanishing ideal globally, including chart endpoints. On z=c(1,t,…,t^d) its value is c^(4d−2)W(t,H). Nonzero c then gives Incidence⇒W(t,H)=0. This is the missing concrete polynomial witness required for the isotropic-image containment.

IsotropicChartCover proves from the actual denominator that every isotropic curve representative has a≠0. At (0,1) the binary denominator is one; scaling by a nonzero b cannot make it zero. Thus moving every isotropic point to the affine chart loses no point at infinity. The scalar c a^d is proved nonzero, and the true bilinear denominator scales by c², not an absolute-value square.

For the forward raw-image inclusion, Ramification supplies its original Incidence, the chart cover supplies D(t)=0, and the global critical witness supplies W(t,H)=0. Since the actual D has simple roots, W=−ND′ at t forces N(t)=0. Consequently every point of the literal IsotropicImage lies on one of the actual numerator-evaluation hyperplanes.

For the reverse inclusion, D(t)=N(t)=0 gives both W(t,H)=0 and W′(t,H)=0 by the genuine common-root homogeneous-partial calculation. The discharged chart theorem constructs an actual full-ideal Ramification witness at (1,t), with zero denominator. This proves membership in the **raw** IsotropicImage, without inserting any projection closure. It works for every nonzero H, including zero numerators, matrix-to-numerator kernel points and all N=cD. The uniform positive-d argument includes d=2.

IsotropicDegree now proves the exact zero-set equivalence for every nonzero matrix and supplies the already proved nonzero, squarefree, degree-2d homogeneous evaluation product as the witness in the unchanged HasReducedDegree definition. This counts every reduced component and establishes a genuine hypersurface equation. The isotropic endpoint does not depend on pending family-discriminant nonvanishing or multiplicity-one arguments. Those remain obligations for the other conjunct.

## Scope and reproduction

Run reproduce.py against the shared Git object store with the pinned compiler/cache, a new private --build directory and owned --output directory; then run endpoint_closure.py. The actual independent build was /private/tmp/nla-tr26-isotropic-4692336f-verification. Exact commands, source hashes, original-input checks, kind/axiom lists and raw logs are retained here.

The main 36-module/kernel replay passed on its first run. The auxiliary import-classification helper initially omitted the builtin Lean runtime from its permitted external-module list; its corrected classification passes, and the original metadata diagnostic is retained under attempts/closure-runtime-import. No Lean source or compiler check changed for that bookkeeping correction.

I authored no accepted source, canonical edit, ID change or statement modification. Mathematical credit remains with Matthew J. Colbrook; implementation and review are AI-agent work, with no external human endorsement claimed. This is a completed exact isotropic endpoint only. The nonisotropic reduced-degree formula, full Target, complete proof promotion and authentic Linux/Comparator receipts require separate work and review.

