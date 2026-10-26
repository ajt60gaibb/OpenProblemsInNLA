#!/usr/bin/env python3
"""Portable offline independent audit of the original final TR26 Linux receipt.
This script does not execute Lean, Comparator or a new Linux job.
"""
import argparse
from pathlib import Path
import subprocess
import sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();here=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(here/'audit_receipt.py'),'--repo',str(a.repo.resolve()),'--evidence',str(here/'retained/run-40400589674/terminal'),'--output',str(a.output.resolve()),'--head','240e607ddc8f74d19f04e9ea1a64fe2bad1762b2','--run','40400589674','--metadata',str(here),'--approved-package-review',str(here/'prior-independent-approvals/APPROVED_PACKAGE_INPUTS.json'),'--promotion-review',str(here/'prior-independent-approvals/PROMOTION_INPUTS.json'),'--expected-receipt',str(here/'INDEPENDENT_RECEIPT_IDENTITIES.json')],check=True)
