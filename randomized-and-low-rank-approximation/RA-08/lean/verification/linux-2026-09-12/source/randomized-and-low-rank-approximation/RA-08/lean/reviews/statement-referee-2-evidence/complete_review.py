"""Complete root RA08 statement postchecks without rerunning successful Lean commands."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

R=Path('/tmp/nla-lean-ra08-worktree')
P=R/'randomized-and-low-rank-approximation/RA-08/lean'
E=P/'reviews/statement-referee-2-evidence'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda r,*a:subprocess.check_output(['git',*a],cwd=r)
original=Path('/tmp/nla-lean-formalization/review_ra08_statements.py')
(E/'review_statements.initial.py.txt').write_bytes(original.read_bytes())
record=json.loads((E/'fresh-checks.json').read_text())
assert len(record['commands'])==3 and all(c['exit_code']==0 for c in record['commands'])
for c in record['commands']:
    assert sha(Path(c['command'][-1]))==c['source_sha256']
    assert sha(E/c['log'])==c['log_sha256']
log=(E/'Inspect.log').read_text()
raw=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
parsed={name:{re.sub(r'\.\{[^}]*\}$','',a.strip()) for a in atoms.split(',')} for name,atoms in raw}
assert len(parsed)==7
definition_names=['spectralNorm','AdmissibleFunction','ConcaveSpectralTransferConjecture','functionalCalculus','witnessMatrix','witnessGap']
allowed={'propext','Classical.choice','Quot.sound'}
for name in definition_names:assert parsed['NLA.RA08.'+name]==allowed
assert parsed['NLA.RA08.not_concaveSpectralTransferConjecture']==allowed|{'sorryAx'}
assert (E/'Challenge.log').read_text().count('declaration uses `sorry`')==14
assert not (E/'Definitions.log').read_text() and 'warning:' not in log
(E/'postcheck-correction.json').write_text(json.dumps(dict(
    issue='Initial Python postcheck compared bare axiom names against pp.universes=true output such as Classical.choice.{u}; Lean itself succeeded on all three commands.',
    observation='AssertionError at the exact standard-three-name comparison after all three exit-zero source commands.',
    correction='Normalize only displayed trailing universe annotations and whitespace; require exactly the same standard three names on all six definitions. The deliberate Challenge theorem must additionally show sorryAx.',
    initial_script_sha256=sha(E/'review_statements.initial.py.txt'),Lean_rerun=False,
    candidate_or_checker_change=False,actual_axioms={k:sorted(v) for k,v in parsed.items()}),indent=2)+'\n')
freeze=P/'reviews/statement-freeze.json'
assert sha(freeze)=='eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332'
frozen=json.loads(freeze.read_text())
for rel,h in frozen['files'].items():assert sha(P/rel)==h,rel
for rel,h in frozen['source_files'].items():
    assert sha(R/rel)==h
    assert hashlib.sha256(git(R,'show',frozen['base']+':'+rel)).hexdigest()==h
for pin in record['pins']:
    dep=Path(pin['path']);assert git(dep,'rev-parse','HEAD').decode().strip()==pin['rev']
    assert not git(dep,'status','--porcelain=v1')
registry=json.loads((R/'problem_ids.json').read_text());assert len(registry)==217
for rel in registry.values():assert (R/rel).read_bytes()==git(R,'show',frozen['base']+':'+rel)
assert not (P/'Solution.lean').exists() and not (P/'NLA/RA08/Proof.lean').exists()
api_sources={}
cache=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib')
for rel in ['Mathlib/Analysis/Matrix/Order.lean','Mathlib/Analysis/Matrix/Spectrum.lean',
            'Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean','Mathlib/Analysis/CStarAlgebra/Matrix.lean',
            'Mathlib/Analysis/Convex/Function.lean','Mathlib/LinearAlgebra/UnitaryGroup.lean']:
    path=cache/rel
    api_sources[rel]=dict(sha256=sha(path),bytes=path.stat().st_size,
                          git_blob=git(cache,'rev-parse','HEAD:'+rel).decode().strip())
(E/'actual-api-sources.json').write_text(json.dumps(dict(commit='0df444a360eaa60ab8c11dca51a86af692955474',files=api_sources),indent=2)+'\n')
record.update(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    all_pins_rechecked=True,original_frozen_files_unchanged=39,original_source_blobs_unchanged=10,
    canonical_pages_unchanged=217,definition_only_kernel_reports=6,deliberate_reference_holes=14,
    schema='Actual v0.4 schema PASS with no completed main results. Completion-only repository validator not claimed.',
    parser_correction='postcheck-correction.json; no repeated Lean compilation',
    verdict='PASS: independent exact statement and diagnostic checks; complete theorem proof still absent')
(E/'fresh-checks.json').write_text(json.dumps(record,indent=2)+'\n')
report=P/'reviews/statement-referee-2.md'
assert not report.exists()
report.write_text('''# RA-08 independent statement referee 2 — 12 September 2026

**APPROVE the exact frozen statement boundary for proof implementation, subject to the separate second approval and coordinator gate.** This is approval of the full mathematical target, definitions, numerical targets and proposed obligations. None of the fourteen admitted reference theorems is proved by this review.

Reviewer: `/root`, OpenAI Codex agent. `/root/formal_review_standards` authored the formal boundary. Before review I contributed the complementary-compression spectral-gap proof idea; I did not implement the definitions or Challenge. This contribution is disclosed and I must not be counted as an independent final mathematical referee of the resulting proof. No external human review, official Tau Ceti service result, author endorsement or priority is claimed.

The freeze `reviews/statement-freeze.json`, SHA-256 `eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332`, binds **39 project files and ten original source files** at upstream `5830ed4fb06da0659414a3deb2a40ad327aca052`. I independently rehashed every bound byte and source Git blob before and after my checks. Definitions is `8c2f3a76e44730b1f9d5bc8e896070c10868bae817d0c3d11ace22b3c7d94c41`; Challenge is `6dfe1fe49431bd3f5dc4c91360911d02c6aaf73d902a40fcabec79155fb11c18`; numerical targets is `a1fa22ee4cf7b3481795e68f9b04217b4da9761e3adb60c9cb3551ad2e4a1148`. Comparator is `833d78dcda61a6d240fb1c50dd419ba7f95c3a8ddda768b7e1de6a0047359951`.

## Full target correspondence and actual semantics

I read the entire canonical RA-08 statement and Colbrook's complete authored `03_concave_transfer_counterexamples.tex`, including the spectral proof, original contour estimate and ancillary nuclear extension; I separately read every frozen definition, all fourteen Challenge types, numerical plan, source correspondence, manifest and handoff. The targeted negative answer is the entire canonical implication, not the source's stronger numerical ratio or the unrelated nuclear question.

The full proposition quantifies all natural dimensions n≥2, all ranks 1≤k<n, all real symmetric PSD pairs A≥Ahat≥0, all nonnegative continuous nondecreasing scalar-concave functions on the half-line, every allowed ordered orthonormal eigenbasis of each matrix, and every real epsilon≥0. The implication and both factors 1+epsilon have the original direction. There is no generic f(0)=0, strict monotonicity, differentiability, operator monotonicity, simple spectrum, numerical gap, min-max conclusion or algorithmic approximation premise.

The real extension encoding includes every half-line function: its irrelevant negative values can be assigned arbitrarily. `AdmissibleFunction` constrains exactly the half-line. `functionalCalculus_spectral` separately promises extension independence on actual nonnegative spectra. Actual Mathlib `ConcaveOn` was inspected: convex combinations have nonnegative weights summing to one, with the correct concavity inequality.

`OrderedSpectralData` is arbitrary orthogonal Q, nonnegative antitone eigenvalues and exact Q-diagonal-Q-transpose reconstruction. It represents all permitted signs/rotations in repeated eigenspaces. `orderedSpectral_exists` must prove existence for every actual PSD matrix, including empty-dimensional supporting cases; `orderedSpectral_semantics` must prove genuine column orthonormality and eigenvector equations. These separate obligations prevent a vacuous selected-family restriction. A preferred algorithmic decomposition is not substituted.

The two truncations use the SAME Q. Indices i<k are zero based; eigenvalue k is the first omitted value. Discarded transformed coefficients are zero even if f(0)>0, so the expression is the source's f(X)_k and not f(X_k). The generic tail theorem includes k=0 where meaningful and requires k<n, ensuring the selected tail index exists.

I inspected actual compiled definitions and pinned API source. `MatrixOrder` is `(B-A).PosSemidef`, not entrywise order; real PSD includes symmetry. `spectralNorm` explicitly applies `Matrix.toEuclideanCLM` over real Euclidean space and uses the CLM operator norm. It does not rely on the default matrix/function norm. The CFC is Mathlib's genuine real CFC. Its matrix spectrum is finite, explaining why the all-functions spectral identity is meaningful without global continuity. The generic CFC spectral identity, tail norms and Rayleigh inequality are explicit proved obligations, not numerical surrogates.

The library's `eigenvalues₀` is sorted, while its ordinary `eigenvalues` is reindexed and must not be presumed antitone. That pitfall is explicitly documented. The chosen-family structure and existence theorem provide the required ordered bridge. `cfc_mono` applies scalar domination on one fixed matrix's spectrum; it does not give operator monotonicity of the kink function between different matrices.

## Independent numerical reconstruction and remaining bridges

My own exact Fraction program parses the frozen F, t,a,b,c,g and K-vector literals, independently rebuilds the source U-block projection, and checks U-transpose-U=I, F²=F, the exact sixth-coordinate eigenpair, positive LDL pivots of A and the complementary compression bound. It computes the polynomial matrix expression directly and checks the actual vector image, its squared norm and the full Rayleigh equality. It also independently expands all coefficients of 1-h(a+z). These are finite statement diagnostics only, never a proof oracle or an inferred eigenvalue-count theorem.

The source witness remains n=6,k=3,t=1/65536, a=17/16,b=127/128, f(x)=min(x,1), Ahat=diag(1/2,b,a,0,0,0), A=Ahat+tF, w=(4,3,1,0,0,0). The exact gap is

```
78605142319958855341529309 / 11432529876841442781954048000 > 0.
```

The exact scalar minorant h(x)=x-c*x²*(x-1/2)²*(x-b)², with c=67108864/1896129, is required only on the spectrum that must first be proved to lie in [0,1] union [17/16,infinity). For x≤1 its square-product bound has the correct direction; for x=a+z every shifted coefficient is nonnegative. Its identification with genuine polynomial CFC and PSD domination by f(A) remain explicit unconditional witness obligations.

The compression argument still must be proved using actual nonzero eigenvectors. Likewise the fourth eigenvalue t, all selected truncation identities and true optimal tails must be derived from the matrices. They are not hypotheses of the full negation. Positive LDL diagnostics do not replace these universal spectral arguments. The promised conclusion works for EVERY permitted witness eigendecomposition and refutes the original implication at epsilon zero.

The unnormalized vector and three matrix-vector products avoid approximate eigenvalues, square roots, contour integration and interval subdivision. Only the positive rational gap should receive a material explicit kernel LeanCert singleton certificate; the final proof must consume that actual checker through Rayleigh comparison and full negation. Its weaker strict gap still settles the full original target. The stronger source ratio 334583/15769728, ancillary Nyström identity, all-C extension and nuclear/strictly-increasing extensions are not advertised among these fourteen exports.

## Fresh checks, review angles and verdict limits

Three independent direct-source Lean 4.33.1 commands passed in my own empty project prefix: Definitions, Challenge, and an actual-type/definition inspector. All ten dependency revisions were independently checked clean before and after and reused read-only from MI-22. No previous RA-08 project object was available in that prefix. No Lake build, dependency download/copy, proof implementation or Linux Comparator run was performed. The fourteen Challenge warnings are deliberate; definitions and inspector have no warnings. Six definition-only `#assert_trust kernel` checks and their actual axiom reports use exactly the standard three. A separate print deliberately confirms the final Challenge still depends on `sorryAx`; it is not a completed theorem.

My initial Python postcheck expected bare axiom names even though the inspector enabled printed universes. All three Lean commands had already passed. The preserved initial script and `postcheck-correction.json` record normalization of display-only universe suffixes; the allowed axioms did not change. No Lean command was repeated and no frozen source changed. The actual v0.4 schema passes with no completed main results; no completion-only validator result is claimed. All 217 original canonical pages remain byte-identical and Solved status is unchanged.

The review applies the repository's pinned Tau Ceti adaptation: correctness and scope through full quantifiers and all semantic bridges; proof quality through a concrete finite route with explicit outstanding obligations; reuse through actual Mathlib CFC/order/Euclidean APIs and the Schiffer/Forsythe separation/kernel workflow; generality through ties, f(0)>0 and zero-dimensional supporting cases; API, naming and placement through proof-independent Definitions and separately admitted Challenge; documentation and attribution through honest pending status, exact freezes and preserved authorship. These are scope-appropriate AI-agent review angles, not an official external service result.

George Stepaniants receives formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, without a contact email. Colbrook retains the mathematical source counterexample and original contour proof; Persson, Meyer and Musco retain the question. New formalization licensing does not relicense their source manuscript.

**No statement correction is required.** Approval applies only to the exact frozen bytes and all fourteen proposed obligations. Any mathematical boundary change requires renewed statement review. Implementation, two independent final mathematical reviews, actual Linux Comparator/default-kernel/controls, independent operational inspection and publication review remain required before any status promotion or PR. Neither the author nor a proof-route/implementation coauthor counts as its own independent final referee.
''')
(E/'complete_review.py').write_bytes(Path(__file__).read_bytes())
outer=E/'EVIDENCE-MANIFEST.json'
assert not outer.exists()
files={p.relative_to(E).as_posix():dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(E.rglob('*')) if p.is_file() and p!=outer}
files['../statement-referee-2.md']=dict(bytes=report.stat().st_size,sha256=sha(report))
outer.write_text(json.dumps(dict(file_count=len(files),files=files,
    inventory_rule='Every file in this evidence directory except this exact outer manifest, plus the adjacent referee report; nested manifests are never excluded by basename.'),indent=2)+'\n')
print(json.dumps(dict(verdict='APPROVE exact frozen statement only',report_sha256=sha(report),
                     manifest_sha256=sha(outer),bound_files=len(files),fresh_commands=3),indent=2))
