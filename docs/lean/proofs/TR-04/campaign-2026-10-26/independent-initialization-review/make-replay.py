#!/usr/bin/env python3
"""Derive this scoped driver from the sealed exact-name main-phase auditor."""
from pathlib import Path
import hashlib, json
BASE = Path(__file__).resolve().parent
original = BASE.parent / 'independent-main-phases-review/replay.py'
text = original.read_text()
needle = "'NLA.Proofs.TR04.ttFirstSelection_nonzero_reals'}"
assert text.count(needle) == 1
text = text.replace(needle, "'NLA.Proofs.TR04.ttFirstSelection_nonzero_reals','NLA.Proofs.TR04.ttInitScalar_nonzero_reals'}")
# Use the same type bytes, but a tactic proof like the original theorems.
# This prevents a let-valued conclusion from consuming a term-proof assignment.
needle = "f'\\nexample{header} := @{name} '+ ' '.join(args)+f'\\nend {prefix}\\n'"
assert text.count(needle) == 1
text = text.replace(needle, "f'\\nexample{header} := by\\n  exact @{name} '+ ' '.join(args)+f'\\nend {prefix}\\n'")
text = text.replace('Independent five-block fresh kernel replay', 'Independent complete initializer fresh kernel replay')
(BASE / 'replay.py').write_text(text)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
(BASE / 'driver-provenance.json').write_text(json.dumps({
    'prior_driver': str(original), 'prior_sha256': sha(original),
    'driver_sha256': sha(BASE / 'replay.py'), 'changes': [
        'Add the exact Prop-valued initializer NeZero instance to expected theorem-kind names.',
        'Keep each literal header byte-for-byte and apply the original theorem using a by-exact proof to delimit let conclusions.',
        'Update the driver description only.'
    ], 'trust_guards_removed': False, 'proof_source_changes': False
}, indent=2) + '\n')
