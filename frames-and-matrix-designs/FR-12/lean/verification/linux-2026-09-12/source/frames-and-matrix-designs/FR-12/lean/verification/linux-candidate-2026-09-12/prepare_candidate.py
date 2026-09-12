from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import yaml

REPO = Path('/tmp/nla-lean-fr12-worktree')
PROJECT = REPO / 'frames-and-matrix-designs/FR-12/lean'
OUT = PROJECT / 'verification/linux-candidate-2026-09-12'
FREEZE_SHA = 'c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87'
REV = '8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc'
AFFILIATION = 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

freeze_path = PROJECT / 'reviews/proof-freeze.json'
assert sha(freeze_path) == FREEZE_SHA
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 74 and len(freeze['source_files']) == 4
assert not (PROJECT / 'formalization.yaml').exists()
assert not OUT.exists(), 'Do not replace candidate evidence'
inputs = {}
for key, base in [('files', PROJECT), ('source_files', REPO)]:
    for name, expected in freeze[key].items():
        assert sha(base / name) == expected, name
        inputs[str((base / name).relative_to(REPO))] = expected
reports = {
    'reviews/statement-referee-1.md': '1f5dacc0d57302b09a2c25c71372c1527d01b3f0b247a9183b1130e4a45fd2fe',
    'reviews/statement-referee-2.md': 'd288c647cedf362609a2630c8072ba66331e04d572ca11632cf6065110581e54',
    'reviews/proof-referee-1.md': 'b0f455ab34b6d79a0f7fd5c9560a5e1b67eb4bf4a2a6d85772d87e6549428d6f',
    'reviews/proof-referee-2.md': '253962587f197745f234aec95b4a3570b3f4f0e4d55feb37bdca6372d62490a9',
}
for name, expected in reports.items():
    assert sha(PROJECT / name) == expected, name
OUT.mkdir(parents=True)
archived = OUT / 'frozen-statement-stage-README.md'
shutil.copyfile(PROJECT / 'README.md', archived)
assert sha(archived) == freeze['files']['README.md']
registry = json.loads((REPO / 'problem_ids.json').read_text())
before = {
    'stage': 'Before Linux candidate metadata; proof complete with two independent final approvals',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'proof_freeze_sha256': FREEZE_SHA,
    'all_original_74_project_plus_4_source_inputs': inputs,
    'report_sha256': reports,
    'archived_README_sha256': sha(archived),
    'canonical_pages': {ident: sha(REPO / path) for ident, path in registry.items()},
    'problem_ids_sha256': sha(REPO / 'problem_ids.json'),
    'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
    'canonical_status': 'Solved',
}
(OUT / 'inputs-before.json').write_text(json.dumps(before, indent=2) + '\n')

readme = r'''# FR-12 Lean formalization

The complete original labeled real Hadamard counting conjecture is refuted by
the implemented proof. All seven exports passed local Lean checks, two
independent statement reviews and two independent final proof reviews.
**Actual Linux Comparator, separate default-kernel replay and their operational
audit are pending.** The canonical status remains **Solved**.

**Mathematical proof and formalization:** George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA, with substantial AI-agent assistance.
Ferber, Jain and Zhao retain the original conjecture and published-upper-bound
credit. Independent AI-agent reviews are not external human peer review,
official Tau Ceti endorsement or historical-priority certification.

## Complete original target

For each positive integer `n`, `H(n)` counts individual labeled real sign
matrices satisfying the actual Gram identity `A * A.transpose = n • 1`.
There is no quotient by signed permutations or normalization of the matrices.
The full assertion asks for a single positive real `C` such that

```math
H(n)\leq 2^{C n\log_2 n}
```

for every positive natural `n` divisible by four. [Definitions](NLA/FR12/Definitions.lean)
use this exact subtype, actual `Nat.card`, genuine real exponentiation and
`Real.log n / Real.log 2`. The proof establishes that the subtype is finite in
every dimension; it does not assume finiteness to conceal an infinite count.
At every positive dimension it also proves equivalence to Mathlib's actual
`Matrix.IsHadamard` predicate.

The complete [canonical target](../README.md) and George's
[informal proof](../solution.md) are retained at source revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. See the unchanged
[numerical targets](NUMERICAL_TARGETS.md) and [source map](SOURCE_MAP.md).
Their statement-stage labels record the original approved boundary; this guide
describes the current proof/review status.

## Exact proof and advertised exports

For arbitrary order-`m` Hadamard matrices `A`, `B` and a permutation `σ`, the
actual construction has top rows `(A_i,B_i)` and bottom rows
`(A_(σ i),-B_(σ i))`. The top halves recover both original labeled matrices;
the bottom first half and proved row injectivity recover the permutation.
Every output is Hadamard. Counting this actual injection proves

```math
m!\,H(m)^2\leq H(2m)\qquad(m\geq1).
```

**The formally proved recurrence has factor `m!`.** The source's stronger
all-perfect-matching factor `(2m−1)!!` is outside these exports. The smaller
family already proves the exact source lower bound and the full canonical
negation, with no restriction on the count or conjecture being refuted.

[Semantics](NLA/FR12/Semantics.lean) proves finite counting and genuine row
orthogonality. [Doubling](NLA/FR12/Doubling.lean) proves the block entries,
Hadamard property, injectivity and cardinality comparison.
[Growth](NLA/FR12/Growth.lean) begins with an actual order-one matrix and
derives positivity at every power of two, an exact factorial bound and

```math
H(2^{k+2})\geq2^{\,2^{k+2}k(k+1)/8}\qquad(k\in\mathbb N).
```

This is exactly the source bound at `K=k+2`. The inner exponent `k+2` is
natural; the outer exponent is real. Direct induction on the exponential
inequality avoids logarithms of the count and asymptotic factorial estimates.
For every positive real `C`, Archimedean choice supplies `k>16C+2`; the proved
strict exponent gap and the actual base-two logarithm identity give a positive
multiple-of-four order violating that `C`'s proposed bound.

The [frozen Challenge](Challenge.lean) and [completed Solution](Solution.lean)
have these seven declarations, each with prefix `NLA.FR12.`:

| Declaration | Complete scope |
| --- | --- |
| `counting_semantics` | Actual finite matrix count in every dimension and equivalence to Mathlib Hadamard matrices in positive dimension. |
| `injective_doubling` | Every output of the concrete map is Hadamard and the map is injective for all `m≥1`. |
| `factorial_doubling` | The actual cardinalities satisfy `m! H(m)²≤H(2m)` for all `m≥1`. |
| `power_two_nonempty` | A positive count at every order `2^k`, including order one. |
| `power_two_lower_bound` | The displayed exact quantitative bound for every natural `k`. |
| `counterexample` | Every positive real constant fails strictly at a power-of-two multiple of four. |
| `not_countingConjecture` | Unconditional negation of the complete original counting assertion. |

The formalization does not claim the stronger matching recurrence, Hadamard
existence at every admissible order, a matching upper bound or historical
priority. The only source-signature difference is the harmless alpha-renaming
of the unused bound variable `hn` to `_hn` in `counting_semantics`; its original
positive-dimension premise remains intact. Challenge is byte-identical.

## Kernel trust and independent reviews

The pins are Lean **4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926)
and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
Proof and Solution explicitly select `leancert.trust "kernel"`.
**LeanCert performs actual kernel trust auditing of this exact proof. There is
no numerical interval certificate, root approximation or interval subdivision.**
The symbolic injection and direct exponential induction avoid large matrix,
matching or integer enumeration in Lean.

All fourteen internal/public source `#assert_trust kernel` checks and their
transitive axiom reports pass with exactly `propext`, `Classical.choice` and
`Quot.sound`. Each independent final referee freshly reran the source modules
and seven additional public kernel assertions. Both traversed all 49 reached
project declarations and confirmed the actual material mathematical dependencies.
There are no proof-development or definition holes, custom axioms or native
proofs. Solution does not import Challenge. The seven intentional Challenge
placeholders are isolated and excluded from proof-development sorry counts.

- Statement approvals before implementation: [referee 1](reviews/statement-referee-1.md)
  and [referee 2](reviews/statement-referee-2.md).
- Independent final approvals: [referee 1](reviews/proof-referee-1.md)
  and [referee 2](reviews/proof-referee-2.md).
- [Proof-start record](verification/proof-start.json),
  [complete proof freeze](reviews/proof-freeze.json) and
  [author handoff](reviews/proof-completion.md).
- Independent raw evidence: [referee 1](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json)
  and [referee 2](verification/final-referee-2/evidence-manifest.json).
- [v0.4 manifest](formalization.yaml), [Comparator configuration](comparator.json),
  [dependency pins](lake-manifest.json) and
  [candidate preservation evidence](verification/linux-candidate-2026-09-12/).

The author's 2157-job build and the independent fresh-source checks are local
macOS runs with matching compiled dependency reuse at ten clean pinned Git
revisions. They do not claim all Mathlib dependencies were rebuilt from source
or that the Linux verifier ran. The relevant
[pinned Tau Ceti standards](../../../docs/lean/REVIEW.md) were applied within
the scope of this complete original target.

## Reproduction and pending Linux gate

From this directory with its exact toolchain and manifest:

```
lake exe cache get
lake build Solution
lake env lean Solution.lean
```

After the candidate has an immutable Git revision, use the repository's
[shared workflow](../../../docs/lean/README.md) on a correctly configured
[non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  frames-and-matrix-designs/FR-12/lean \
  /absolute/path/to/nla-lean-tools
```

The actual run must build/export the independently checked Challenge and
Solution, compare all seven declarations with no definition exceptions, replay
the proof through Lean's default kernel, and pass the real isolation and
rejection controls. [Comparator](comparator.json) permits only the three
standard axioms. No FR-12 Linux run or operational PASS is claimed yet.

The exact historical README is archived at
[the frozen statement-stage copy](verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md).
Only this current README changes among the 74 proof-freeze inputs; the other
73, all four original sources, all mathematical statements/proofs, pins,
configuration and both statement/final review reports remain unchanged.
The current manifest and candidate records describe completed local gates and
pending Linux verification. Canonical status remains Solved until actual
verification evidence receives its separate operational and publication review.
'''
(PROJECT / 'README.md').write_text(readme)

axioms = ['propext', 'Classical.choice', 'Quot.sound']
config = json.loads((PROJECT / 'comparator.json').read_text())
scopes = [
    'Finiteness of the exact labeled real Hadamard subtype for every dimension and equivalence to Mathlib IsHadamard in positive dimension.',
    'Hadamard validity and injectivity of the exact two-matrix/permutation construction for every positive order.',
    'The exact full-subtype cardinalities satisfy m! H(m)^2 ≤ H(2m) for every m≥1.',
    'Actual nonempty labeled Hadamard matrix sets at every power-of-two order, including order one.',
    'The exact source lower bound H(2^(k+2)) ≥ 2^(2^(k+2) k(k+1)/8) for every natural k.',
    'Every positive real proposed constant has a strict counterexample at some positive power-of-two multiple of four.',
    'Unconditional negation of the complete original all-dimension labeled-matrix counting conjecture.',
]
metadata = {
    'version': 'v0.4',
    'project': {
        'name': 'FR-12: a labeled Hadamard counting counterexample',
        'description': 'Proves a complete negative answer to the original labeled real Hadamard counting conjecture. A genuine finite matrix subtype and an injective restricted doubling construction give m! H(m)^2 ≤ H(2m), the exact source power-of-two lower bound, and a counterexample for every positive real constant.',
        'authors': ['George Stepaniants'],
        'affiliations': {'George Stepaniants': AFFILIATION},
        'responsible_maintainers': ['George Stepaniants'],
        'license': 'Apache-2.0',
    },
    'repository': {'role': 'substantive-development'},
    'sources': [
        {'title': 'FR-12 — Counting real Hadamard matrices',
         'id': f'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/{REV}/frames-and-matrix-designs/FR-12/README.md',
         'type': 'web-post', 'location': 'Complete original Statement', 'relationship': 'formalizes',
         'author_endorsement': 'not-contacted',
         'note': 'Retains the individual labeled sign-matrix count, arbitrary positive real C, every positive natural dimension divisible by four and the genuine base-two logarithm. The source is already informally Solved; this candidate does not promote its canonical status.'},
        {'title': 'FR-12: A matching-indexed doubling counterexample', 'authors': ['George Stepaniants'],
         'id': f'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/{REV}/frames-and-matrix-designs/FR-12/solution.md',
         'type': 'manuscript', 'location': 'Exact target, Lemma 1 and Theorem 1', 'relationship': 'adapts',
         'author_endorsement': 'participated',
         'note': 'George supplied the mathematical manuscript and requested its formalization. This records source-author participation, not external human peer review or endorsement of a completed Linux result. The formal construction uses only top-to-bottom matchings, giving m! instead of the source’s stronger (2m−1)!! recurrence; it still proves the identical quantitative lower bound and full original negation. Direct induction on real exponentials avoids logarithms of the count.'},
        {'title': 'On the number of Hadamard matrices via anti-concentration',
         'authors': ['Asaf Ferber', 'Vishesh Jain', 'Yufei Zhao'],
         'id': 'https://doi.org/10.1017/S0963548321000377', 'type': 'article',
         'location': 'Published Conjecture 1.3 and Theorem 1.2', 'relationship': 'background',
         'author_endorsement': 'not-contacted',
         'note': 'Original counting conjecture and published upper-bound attribution. No unproved external theorem is assumed by the Lean proof.'},
    ],
    'related_formalizations': [
        {'id': 'https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof',
         'relationship': 'other', 'note': 'Campaign reference for statement-first organization, explicit kernel LeanCert trust auditing and the shared pinned Comparator/exporter workflow. Reuse and licenses are retained in tools/lean/NOTICE.md. No Forsythe mathematical theorem is assumed.'},
        {'id': 'https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1',
         'relationship': 'other', 'note': 'Organizational example studied in the campaign. No Schiffer mathematical theorem or proof source is imported.'},
    ],
    'automation': {
        'methods': [{'method': 'agent', 'framework': 'OpenAI Codex',
                     'tool_setup': 'Multiple agents; two independent statement approvals before implementation, exact pinned Mathlib matrix/cardinality/factorial/real-power APIs, two independent final referees with separate fresh artifact prefixes, and actual LeanCert kernel trust assertions.',
                     'prompting_notes': 'Preserve the complete original all-dimension and all-positive-real-constant conjecture. Prove actual finite subtype semantics and injectivity, not assumed family cardinalities. Restrict only the constructed matching family to m! choices, retain the exact source lower bound, and use direct exponential induction and Archimedean choice. Avoid large enumeration, approximate logarithms or decorative interval certificates.'}],
        'notes': 'Substantial AI assistance requested by George Stepaniants. The implementation agent /root is not counted as an independent referee. Independent reviewers are /root/formal_review_standards and /root/leancert_examples. No external human peer review, official Tau Ceti endorsement, unrecorded model identity, monetary-cost measurement or historical-priority certification is claimed.',
    },
    'status': {
        'scope': 'Complete negative answer to the original canonical labeled real Hadamard counting question, with all seven advertised exports implemented. Local Lean elaboration, fourteen implementation/public kernel-trust and standard-three axiom checks, two independent statement approvals and two independent final proof approvals passed. Actual sandboxed Linux Comparator, separate default-kernel replay, isolation/rejection controls and an independent operational audit are pending. Canonical status remains Solved. The stronger all-matching recurrence and existence at every admissible order are outside the formal scope.',
        'sorry_count': 0, 'sorry_in_definitions': 0, 'axioms': axioms,
        'main_results': [{'declaration': name, 'file': 'Solution.lean', 'sorry_count': 0,
                          'axioms': axioms, 'comparator_config': 'comparator.json',
                          'literature_dependencies': []} for name in config['theorem_names']],
    },
    'fidelity': {'divergences': 'The count is the actual labeled real sign-matrix subtype, with an unconditional finiteness proof; no quotient or normalization is used. The n=0 definition extends the count harmlessly while the conjecture retains only positive dimensions. A restricted top/bottom matching injection proves m! H(m)^2 ≤ H(2m), not the stronger informal (2m−1)!! factor. The exact source lower bound and complete original target negation remain unchanged. The index K=k+2 avoids truncated natural subtraction; the inner exponent is natural and outer exponent real. The sole public source-signature variation is alpha-renaming the unused hn binder to _hn in counting_semantics, retaining its premise. The frozen Challenge itself is unchanged.'},
    'review': {
        'status': 'agent-reviewed; local Lean proof checks passed; Linux Comparator pending',
        'reviewers': ['OpenAI Codex agent /root/formal_review_standards: independent statement referee 1 and final proof referee 1',
                      'OpenAI Codex agent /root/leancert_examples: independent statement referee 2 and final proof referee 2'],
        'notes': 'Both independent statement approvals preceded implementation. Both independent final referees read the complete original source and proof, re-elaborated eight modules/inspection commands in new target prefixes, and audited actual mathematical types and dependencies. All fourteen source and seven additional public kernel assertions per referee passed. Each referee traversed all 49 reached project declarations; the first required 20 material dependencies and the second 25. All public theorem axiom sets are exactly propext, Classical.choice and Quot.sound. The seven deliberate Challenge placeholders are isolated and excluded from proof-development sorry counts. Matching compiled dependency caches at ten clean pins were reused on macOS; a full dependency source rebuild or Linux run is not claimed. LeanCert performs kernel trust auditing only; no interval certificate is claimed. The relevant pinned Tau Ceti rubrics were applied within the scope of this target. The historical README is archived at verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md; only the current README differs among the 74 proof-freeze inputs, with all remaining 73, four original sources, mathematical files, configuration, pins and all four report hashes preserved. No external human peer review is claimed.',
        'statement_reports': [{'file': name, 'sha256': reports[name]} for name in ['reviews/statement-referee-1.md', 'reviews/statement-referee-2.md']],
        'proof_reports': [{'file': name, 'sha256': reports[name]} for name in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']],
        'proof_freeze': {'file': 'reviews/proof-freeze.json', 'sha256': FREEZE_SHA},
        'linux_verification': {'status': 'pending', 'note': 'No project-specific FR-12 Linux run or operational PASS has been recorded for this candidate. Canonical status remains Solved until those separate gates are complete.'},
    },
    'alignment': [{'declaration': name, 'scope': scope} for name, scope in zip(config['theorem_names'], scopes)],
    'acknowledgements': 'George Stepaniants for the supplied proof; Ferber, Jain and Zhao for the original conjecture and prior upper bound; Mathlib and LeanCert contributors for proved matrix, finite-cardinality, factorial, real-analysis and kernel-audit APIs. Shared Comparator/exporter and Landrun reuse is separately credited with its licenses. No external mathematical theorem is assumed as a custom axiom.',
}
header = '# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json\n'
(PROJECT / 'formalization.yaml').write_text(header + yaml.safe_dump(metadata, sort_keys=False, allow_unicode=True, width=100))
for name, expected in freeze['files'].items():
    if name != 'README.md':
        assert sha(PROJECT / name) == expected, name
assert sha(archived) == freeze['files']['README.md']
print('Prepared FR-12 current README, actual v0.4 manifest and exact historical archive; Linux remains pending.')
