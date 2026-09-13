# RA-07 complete local proof — frozen for independent final review

The complete six-export implementation passes local Lean compilation. The original canonical assertion is proved affirmatively for every `n ≥ 3`, every tuple of strictly positive real numbers, and every original index `2 ≤ j ≤ n−1`. Two independent final proof reviews, actual Linux Comparator/kernel replay, publication metadata and any canonical verification promotion remain pending. This report does not claim those later checks have passed.

Mathematical source: Matthew J. Colbrook, *Convexity of a volume-sampling error sequence*, Theorem 1.1, in the retained repository source at revision `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. No George email is included. Existing Mathlib/LeanCert authorship remains with its sources.

## Statement gate

Both independent statement reviews approved the exact statements before any proof code was created:

- Referee 1 SHA-256: `54481c9106ca42702d1932eda6471e000c7aeb1b046f58a2061318b08ec0478e`.
- Referee 2 SHA-256: `7e4210428973b3b7da4a2a4d37e41556134ff932f1f4c4cbab31354eba687009`.
- The statement freeze SHA-256 is `ef989bac80cf7a9c671557ff45305b56a7f4d11701bbcb44336a5a1448e8c803`.

`verification/proof-start.json` records the gate timestamp and input hashes. Definitions, Challenge, NUMERICAL_TARGETS, SOURCE_MAP, all dependency pins and Comparator configuration are unchanged. The final fresh check verified 32 bound source, statement, configuration, evidence and implementation inputs unchanged during validation. The original canonical README, original source manuscript, source review and problem ID were not edited.

## Complete implementation

| Source | SHA-256 |
| --- | --- |
| `NLA/RA07/Algebra.lean` | `1be33b680d0f66d793a564ec22aae8996474aa85f7699f4d1dff6639903cf013` |
| `NLA/RA07/Roots.lean` | `ccbb931696ed1fafcda2518daaccee8eacb201a10eaedefd694f573b44adecde` |
| `NLA/RA07/Sums.lean` | `6a1410ed2efe6155f2f27c22b8afe37ffd0110812850f0d336c9ffee2dd8050b` |
| `NLA/RA07/Proof.lean` | `20c4d2a1078495b442f74126b42e0960462a1e82e3c5aec0b2c09065921dd21d` |
| `Solution.lean` | `55ea9b34825481eb10fefc6409eab16db61849663849f2ca09f6ceb8a1857114` |

The public declarations are `NLA.RA07.elementary_values`, `generating_derivative_values`, `positive_derivative_factorization`, `power_sum_certificate`, `second_difference_certificate`, and `errorSequence_convex`. Their signatures match the six frozen Challenge declarations verbatim; the retained Comparator selects exactly these six and no definition-name exceptions.

`Algebra.lean` proves the empty/oversized/positive elementary subset-sum facts. It connects the actual product polynomial to the actual subset sums using Mathlib's `Finset.prod_one_add` and coefficient extraction, then applies `Polynomial.coeff_iterate_derivative` to obtain the factorial-scaled derivatives at zero. This direct product expansion replaces the initially considered multiset elementary-symmetric API; it proves the same frozen statements for every real tuple and natural coefficient index.

`Roots.lean` proves the generating polynomial's degree and inductively obtains the exact derivative degree from Mathlib's characteristic-zero `Polynomial.natDegree_derivative`. It does not infer equality from the weaker iterated-degree upper bound. Actual complex roots of the generating polynomial lie on the open negative real ray. The ray is convex, so actual Mathlib Gauss–Lucas preserves the root location at every relevant derivative. The polynomial splits over the complex numbers; `Splits.of_splits_map` descends this splitting to the reals. `Splits.eq_prod_roots` and the exact root-multiset cardinality retain all multiplicities. Enumerating the full multiset as a list of length equal to the degree produces exactly the required positive reciprocal-root tuple, and evaluation at zero determines the normalization constant. No root table, factorization or polynomial degree is assumed.

The final derivative case `d = n` is included: its degree is zero, the root multiset and factor tuple are empty, its product is one, and the strictly positive scale is the actual derivative value. The generic real factorization helper also handles the zero polynomial correctly, although the relevant derivatives here have a separately proved positive constant term.

`Sums.lean` proves the first three actual derivatives of an arbitrary finite linear-factor product by finite-set induction and exact polynomial differentiation. It then proves both ordered-pair identities:

`s1*s3 − s2^2 = Σ(a<b) μa*μb*(μa−μb)^2`,

`s1^2 − s2 = 2*Σ(a<b) μa*μb`.

The proof counts each unordered pair once by splitting a symmetric double sum. All pair terms are nonnegative. When at least two factors remain, the pair of indices zero and one gives a strictly positive term; thus the second identity supplies exactly the positive denominator argument specified before implementation. No distinctness condition is added and the final gap may be zero.

`Proof.lean` connects each original elementary-symmetric ratio with consecutive actual derivatives. Actual iterated differentiation proves that a factorization at derivative order `d` transfers every shifted ratio to the corresponding ratio of the factor tuple; the nonzero scale cancels even when a numerator is zero. At the original index `j`, the implementation uses exactly `d = j−1` and `m = n−(j−1)`. The first three actual derivative identities give the exact second-difference certificate, and its nonnegative numerator and strictly positive denominator give the full affirmative result. The original degree-two endpoint, `j = n−1`, and the smallest dimension `n = 3` are included without a limiting argument or removed set.

The source's strict monotonicity, additional convexity index one, determinantal sampling identity, Jensen application and stable-rank estimates are outside the published formal scope. Their exclusion does not narrow the original canonical convexity assertion.

## Fresh local validation and trust

An initial complete `lake build Solution` passed with 2,893 jobs. The final retained validation then freshly elaborated Definitions, Algebra, Roots, Sums, Proof, Solution and the separate Challenge into a new output prefix, excluding all old project `.olean` files from `LEAN_PATH`. A final independent-of-the-proof inspection module also compiled. Every command returned zero. The implementation modules emitted no warnings; the isolated Challenge had exactly its six deliberate placeholder warnings.

This validation ran on macOS arm64 with Lean 4.33.1, using existing dependency build caches. All ten actual dependency checkouts were checked clean at the manifest pins, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. This is an author check, not an independent final referee or Linux Comparator result; dependency source trees were not rebuilt from scratch.

The 12 source trust assertions and fresh axiom reports—six internal completed targets plus six public exports—passed, each depending only on `propext`, `Classical.choice` and `Quot.sound`. The inspection repeats the six public checks. There are no proof holes, custom axioms, unsafe declarations, native-evaluation shortcuts or imports of Challenge in the implementation.

The inspection follows 60 actual project declarations from the exported results. It verifies retention of actual Gauss–Lucas, real splitting, full root-multiset factorization/cardinality, exact derivative degree and coefficient extraction, together with the project pair identities, true derivative formulas and shifted-ratio bridge. It therefore checks that these are participating mathematical dependencies rather than unused supporting declarations.

As approved at the statement stage, this universal theorem uses exact algebra and root geometry throughout. LeanCert provides the actual `#assert_trust kernel` checks. There is no artificial interval certificate, numerical sample grid, approximate root computation or floating-point inference. The earlier finite rational diagnostics remain supplementary checks of the statement draft and do not establish the universal theorem.

## Evidence and handoff

`verification/final_check.py` is the retained author-check driver. `fresh-checks.json` gives every exact command, platform, prefix, source hash, output artifact hash and elapsed time; its SHA-256 is `64f951fdc7d404ee847dbd23e9d7cd5dbce87deed26454e9c0f96703e32dd099`. `inputs-before.json`, `inputs-after.json`, `dependencies.json`, `source-audit.json` and `axiom-audit.json` give the input, pin, statement and trust checks. Raw logs are retained per module.

The actual proof-dependency and semantics inspection log SHA-256 is `e4f9cfb69f9be51b37bce675ef3dd333b9aa8e293467bfde32c71d1b586227e6`. `library-source-hashes.json` binds the read Mathlib and LeanCert sources. `verification/proof-freeze.json` binds the exact implementation, frozen statements/configuration, both statement approvals, this completion report and retained evidence for the two final reviewers.

No canonical status, numbering, Git commit, push or PR was created by this proof implementation. Project README and publication manifest updates are a later packaging task; the existing statement-stage README is retained unchanged for now so its historical hashes remain reproducible.
