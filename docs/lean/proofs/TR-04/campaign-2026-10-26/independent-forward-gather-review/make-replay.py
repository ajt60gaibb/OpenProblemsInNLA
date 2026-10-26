#!/usr/bin/env python3
"""Reuse the exact explicit-name kernel auditor, changing only its description."""
from pathlib import Path
import hashlib,json
BASE=Path(__file__).resolve().parent
prior=BASE.parent/'independent-initialization-review/replay.py'
data=prior.read_text()
assert data.count('Independent complete initializer fresh kernel replay')==1
data=data.replace('Independent complete initializer fresh kernel replay','Independent actual candidate gather and forward phases fresh kernel replay')
(BASE/'replay.py').write_text(data)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(BASE/'driver-provenance.json').write_text(json.dumps({'prior_driver':str(prior),
 'prior_sha256':sha(prior),'driver_sha256':sha(BASE/'replay.py'),
 'changes':['Description only; identical exact-kind, private-name, LeanCert kernel, axiom, lexical, pin, original-input and fresh-object checks.'],
 'trust_guards_removed':False,'proof_source_changes':False},indent=2)+'\n')
