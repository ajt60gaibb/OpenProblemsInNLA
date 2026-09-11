#!/usr/bin/env python3
"""Run finite exact-rational checks: python3 verification/run_all.py"""
from __future__ import annotations
import argparse,json,platform,time
from datetime import datetime,timezone
from pathlib import Path
from exact import serial
from checks import ie13,ie14,ie17,ie18,ie19,ie23

def main():
    if not __debug__: raise RuntimeError('Run without -O: checks use assertions.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('results.json'))
    args=p.parse_args(); start=time.monotonic()
    results={'verified_utc':datetime.now(timezone.utc).isoformat(),'python':platform.python_version(),'arithmetic':'fractions.Fraction; Python standard library only','results':{}}
    for name,check in [('IE-13',ie13),('IE-14',ie14),('IE-17',ie17),('IE-18',ie18),('IE-19',ie19),('IE-23',ie23)]:
        results['results'][name]=check(); print(name+': PASS',flush=True)
    results['analytic_only']=['IE-21','IE-22']
    results['verification_scope']='Finite exact examples and algebra only. General and probabilistic claims require independent review of proof drafts.'
    results['elapsed_seconds']=round(time.monotonic()-start,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(serial(results),indent=2)+'\n',encoding='utf-8')
    print('IE-21/22: analytic drafts, not computationally certified.')
    print('Saved',args.output)
if __name__=='__main__': main()
