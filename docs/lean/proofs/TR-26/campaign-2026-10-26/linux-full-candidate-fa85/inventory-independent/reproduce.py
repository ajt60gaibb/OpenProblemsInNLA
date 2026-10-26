#!/usr/bin/env python3
"""Portable independent offline replay of the retained actual Linux receipt.
No local Lean/Comparator or Linux job is run by this command.
"""
import argparse
from pathlib import Path
import subprocess
import sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True,help='Repository containing all immutable Git objects bound by the receipt')
p.add_argument('--output',type=Path,required=True)
a=p.parse_args(); here=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(here/'audit_receipt.py'),'--repo',str(a.repo.resolve()),'--evidence',str(here/'retained/run-40396604016/terminal'),'--output',str(a.output.resolve()),'--head','fa85c05acc70bbaa05bb3346fb43b57b1546af67','--run','40396604016','--metadata',str(here),'--approved-package-review',str(here/'prior-independent-approvals/APPROVED_PACKAGE_INPUTS.json')],check=True)
