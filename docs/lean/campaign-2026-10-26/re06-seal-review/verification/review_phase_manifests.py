#!/usr/bin/env python3
"""Verify retained original scoped positive manifests, without reinterpreting receipt-only copies."""
import argparse,hashlib,json
from pathlib import Path
EXPECTED={
 'full-source-review':'61facd1585065573f8fa64d5ee15b7574bc602b1ea829f2f12594ce720604119',
 'package-review':'28d5929b6f39ee7408e4343678d635a81961f56bd363fb7a1d981b37b0c62e3a',
 'promotion-review':'35df9158947b2d9f116198806c8d79298d77732cd27005bd8394d4a73e993ce1',
 'final-review':'6a9827f4bccdf7730d376212e5b13f30ad9827f324a4584ec898a97b275cf00a',
}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();checks=[]
 for phase,digest in EXPECTED.items():
  root=a.repo/'docs/lean/proofs/RE-06/campaign-2026-10-26'/phase/'verification';b=(root/'EVIDENCE_MANIFEST.json').read_bytes();ok=sha(b)==digest;checks.append({'check':'verbatim_original_phase_manifest:'+phase,'pass':ok,'sha256':sha(b)});assert ok
  for e in json.loads(b)['files']:
   q=root/e['path'];b=q.read_bytes();ok=sha(b)==e['sha256'] and len(b)==e['bytes'];checks.append({'check':'retained_phase_positive:'+phase+':'+e['path'],'pass':ok});assert ok
 seal=a.repo/'docs/lean/proofs/RE-06/campaign-2026-10-26/FINAL_EVIDENCE_SEAL.json';r={'pass':all(e['pass'] for e in checks),'scope':'Four separately scoped original reviewer positive manifests; their exact hashes were also compared with the original review directories during review. Receipt-only nested copies retain their original external scope.','reviewer':'/root/verification','checks':checks,'seal_sha256':sha(seal.read_bytes()),'script_sha256':sha(Path(__file__).read_bytes())};a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'checks':len(checks)}))
if __name__=='__main__':main()
