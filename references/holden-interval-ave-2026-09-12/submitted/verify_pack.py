#!/usr/bin/env python3
"""Run every delivered exact regression/certificate suite.
Exit nonzero on failure. Universal theorem proofs remain in the Markdown files.
"""
from pathlib import Path
import subprocess,sys,json,time,datetime
ROOT=Path(__file__).resolve().parent
SCRIPTS=[
 'AV-03/test_solver.py',
 'AV-03/test_feedback.py',
 'AV-03/verify_obstructions.py',
 'AV-03/verify_handicap.py',
 'IV-01/build_and_verify_example.py',
 'IV-01/search_boundary_directions.py',
 'IV-01/build_both_boundary_example.py',
 'IV-01/verify_dimension_five.py',
 'IV-01/test_graph_and_certificates.py',
 'IV-01/verify_order_two.py',
]

def main():
    if not __debug__:raise RuntimeError('Run without -O; assertions are part of the tests')
    logs=[];start=time.monotonic()
    for rel in SCRIPTS:
        t=time.monotonic()
        proc=subprocess.run([sys.executable,str(ROOT/rel)],cwd=ROOT,text=True,capture_output=True)
        record={'script':rel,'exit_code':proc.returncode,'elapsed_seconds':time.monotonic()-t,
                'stdout':proc.stdout,'stderr':proc.stderr}
        logs.append(record)
        print(f'{rel}: '+('PASS' if proc.returncode==0 else 'FAIL'),flush=True)
        if proc.returncode:
            print(proc.stdout);print(proc.stderr);break
    out={'all_passed':len(logs)==len(SCRIPTS) and all(x['exit_code']==0 for x in logs),
         'python_version':sys.version,'verification_finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'elapsed_seconds':time.monotonic()-start,'scripts':logs,
         'scope':'Finite exact regression/certificate checks, not formal verification of universal proofs'}
    (ROOT/'verification_summary.json').write_text(json.dumps(out,indent=2)+'\n')
    if not out['all_passed']:raise SystemExit(1)
    print('All exact suites passed.')
if __name__=='__main__':main()
