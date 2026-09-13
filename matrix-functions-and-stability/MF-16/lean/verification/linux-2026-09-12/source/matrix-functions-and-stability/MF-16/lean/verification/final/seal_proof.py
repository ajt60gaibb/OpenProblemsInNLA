"""Freeze the complete MF16 implementation for independent final review."""
from pathlib import Path
import datetime,hashlib,json,subprocess
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=subprocess.run(['python3',str(E/'audit_sources.py')],cwd=P,capture_output=True)
(E/'source-audit.log').write_bytes(r.stdout+r.stderr)
assert r.returncode==0,r.stderr.decode()
audit=json.loads((E/'source-audit.json').read_text())
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
skip={'verification/proof-freeze.json','reviews/proof-completion.md'}
files={}
for q in sorted(P.rglob('*')):
 if not q.is_file():continue
 rel=q.relative_to(P)
 if any(x in {'.lake','.git','__pycache__'} for x in rel.parts) or str(rel) in skip:continue
 assert q.stat().st_size>0 or q.suffix=='.log',str(rel)
 files[str(rel)]=sha(q)
freeze={'phase':'Complete nine-export proof freeze for two independent final mathematical reviews; no Linux result','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':statement['base'],'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),'files':files,'source_files':statement['source_files'],'exclusions':['This exact verification/proof-freeze.json (self)','reviews/proof-completion.md (post-freeze hash-bearing handoff)','.lake/.git/__pycache__ generated or worktree metadata; external compiled prefixes and dependency objects'],'immutable_statement_inputs':45,'original_Git_source_files':14,'fresh_validation_result_sha256':audit['fresh_result_sha256'],'author_source_audit_sha256':sha(E/'source-audit.json'),'pending_gates':'Two independent final reviews, actualv0.4candidate metadata, real Linux Comparator/defaultkernel/controls, operational and publication reviews'}
F=P/'verification/proof-freeze.json';F.write_text(json.dumps(freeze,indent=2)+'\n')
summary=f'''# MF-16 complete proof handoff — 12 September 2026

**Complete implementation; independent final mathematical reviews and actual Linux remain pending.**
All nine frozen contracts compile, including the unconditional negation of the
complete original ordinary-palindrome/all-complex-Hermitian-PD uniqueness claim.
Canonical status remains **Solved**. No commit, push or status promotion is made.

The exact proof freeze is `verification/proof-freeze.json`, SHA-256
`{sha(F)}`. It binds **{len(files)} project inputs and 14 original Git source
files** as direct SHA-256 strings. All **45 original statement inputs** remain
byte-identical. The inventory excludes only itself, this hash-bearing handoff
and the explicitly named generated/cache metadata categories; no nested
evidence manifest is omitted. Both approved statement reports, all raw development
attempts, helper evidence, final fresh logs, source snapshots and author audits
are retained. `verification/PROOF_MAP.md` gives the nine-export source mapping.

| Mathematical file | SHA-256 |
| --- | --- |
'''
for rel,row in audit['math_sources'].items():summary+=f"| `{rel}` | `{row['sha256']}` |\n"
summary+=f'''
Both independent frozen statement approvals preceded the first proof edit; the
accepted gate and the author's explicit before-edit identity check are retained.
The main implementation author is `/root/leancert_examples`; the genuine
Cayley–Hamilton helper author is `/root/solved_statement_inventory`. Root was
a disclosed computation-route contributor. None counts as an independent final
mathematical referee. The assigned final referees are `/root/mf16_final_referee`
and `/root/formal_review_standards`, who authored neither this implementation
nor its statements. Approval remains theirs to determine.

George Stepaniants receives AI-assisted formalization credit with Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA, without an email. Matthew J. Colbrook retains the
mathematical counterexample, and Hillar–Johnson/Armstrong–Hillar retain original
question/source attribution. No new mathematical priority, source-author
endorsement, external human peer review or official Tau Ceti result is claimed.

## Actual complete proof and minimized numerical work

The original B, P and X0, actual list/reversal/occurrence/product semantics and
all complex positive-definiteness quantifiers are unchanged. The genuine
matrix-power theorem uses the actual 2×2 Cayley–Hamilton theorem and a scalar
polynomial remainder. The actual Expr system is proved equivalent in both
directions to determinant three plus two genuine word entries; no residual or
power identity is assumed. Symmetry and true determinant multiplicativity
recover the missing matrix entry. An invertible LDL congruence proves genuine
complex PD; actual ring-homomorphism identities transport the full word.

The one three-dimensional rational box has radius `1/10000000`. The actual
full LeanCert Krawczyk Boolean, exact preconditioner determinant, exact radius
and whole-box contraction bound `<27/1000` are all proved with `decide +kernel`.
The actual retained Boolean helper is
`NLA.MF16.actual_krawczyk_checked._proof_1_1`. It feeds
`LeanCert.Engine.krawczykCheck_sound`, which derives an actual real root in the
box, then all-entry complex matrix recovery, the two distinct solutions and
the complete universal negation. No degree theorem, floating oracle, native
execution trust, extra root assumption, approximate eigenvalue, subdivision or
high-degree interval matrix-power expansion is used. The box-local uniqueness
is distinguished from the disproved global matrix-word uniqueness. Three roots
and the source's exponent-family threshold are outside the nine exports.

## Validation actually performed

The final author run has **10 successful fresh direct-source commands**:
Definitions, Numerical, Algebra, Recovery, Polynomial, CayleyHamilton, Proof,
Solution, an actual-term/dependency inspector, and separately Challenge.
Every project object was initially absent from the fresh private prefix;
all prior MF16 and MI22 project objects were excluded. The toolchain is macOS
Lean4.33.1 at the recorded commit. The ten exact pinned clean MI22 dependency
sources/objects were reused read-only and rechecked afterward. There was no
Lake invocation, dependency copy/download/rebuild, Linux execution or Comparator
run. The actual result SHA-256 is `{audit['fresh_result_sha256']}`.

All implementation modules and inspector passed without warnings. Only the
nine intentional, separately compiled Challenge admissions warn. The source
auditor matched every actual Solution contract to its frozen Challenge text;
the real Linux Comparator still remains a required later gate. All **26**
internal/public/inspection axiom reports contain exactly `propext`,
`Classical.choice` and `Quot.sound`, with corresponding kernel trust assertions.
No proof admission, custom axiom, unsafe/partial project declaration or Challenge
import is present.

The actual fresh inspector traversed types and bodies of **110** reached project
declarations, including the legitimate generated Letter inductive declarations,
and **9** selected LeanCert soundness proofs. It confirmed **35 material
dependencies**, including the actual AD/Jacobian, complete-box contraction,
Banach fixed-point, preconditioner-zero equivalence, matrix characteristic
polynomial, LDL complex PD and full original-negation chain. The source audit
SHA-256 is `{sha(E/'source-audit.json')}`; its raw output and full command/snapshot
records remain adjacent. Development errors and the local disk interruption
are preserved as historical attempts, not reported as successful proof checks.

The current README/numerical/source-map phase notices remain their exact frozen
statement-stage bytes. Candidate packaging must archive the old README, refresh
the live README truthfully and add an actual v0.4 `formalization.yaml` covering
all nine exports before publication. No schema success is claimed now. The
frozen pins, default Challenge target and registered Solution library are
unchanged. Independent final reviews, actual Ubuntu verification and separate
operational/publication acceptance still remain. Please preserve this proof
freeze while reviewing; report any required mathematical correction before edits.
'''
H=P/'reviews/proof-completion.md';H.write_text(summary)
for rel,h in files.items():assert sha(P/rel)==h,rel
print(json.dumps({'verdict':'COMPLETE frozen for independent final reviews','freeze_sha256':sha(F),'handoff_sha256':sha(H),'bound_project_inputs':len(files),'original_Git_sources':14,'fresh_result_sha256':audit['fresh_result_sha256'],'source_audit_sha256':sha(E/'source-audit.json'),'Proof_sha256':sha(P/'NLA/MF16/Proof.lean'),'Solution_sha256':sha(P/'Solution.lean')},indent=2))
