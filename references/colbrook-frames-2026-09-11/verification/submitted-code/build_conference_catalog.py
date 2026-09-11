#!/usr/bin/env python3
"""Reproducibly search, refine, and certify a consecutive dimension range."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import argparse,json,time
from pathlib import Path
from search_conference import run
from certify_conference import generate
from verify_conference import verify


def build(start, stop, directory):
    directory.mkdir(parents=True, exist_ok=True)
    progress = directory/'catalog_progress.jsonl'
    reports = []
    for d in range(start, stop+1):
        t = time.monotonic()
        cert = directory/f'conference_certificate_d{d}.json'
        for seed in range(5):
            candidate = directory/f'conference_d{d}_seed{seed}.json'
            try:
                if not candidate.exists():
                    run(d, seed, 1, 1000, candidate)
                generate(candidate, cert, inverse_bits=32, product_bits=20)
                report = verify(cert)
                reports.append(report)
                (directory/f'conference_certification_d{d}.json').write_text(json.dumps([report],indent=2)+'\n')
                line={'d':d,'passed':True,'seed':seed,'seconds':time.monotonic()-t,
                      'a':report['a_bound_for_norm_MF']['decimal_display_only'],
                      'b':report['b_bound_for_norm_I_minus_MJ']['decimal_display_only'],
                      'K':report['K_norm_M']['decimal_display_only'],
                      'contraction':report['contraction_bound']['decimal_display_only']}
                with progress.open('a') as f:f.write(json.dumps(line)+'\n')
                print('CERTIFIED '+json.dumps(line),flush=True)
                break
            except Exception as exc:
                print(f'ATTEMPT FAILED d={d} seed={seed}: {exc}',flush=True)
        else:
            raise RuntimeError(f'No certificate obtained for dimension {d}.')
        (directory/'catalog_reports.json').write_text(json.dumps(reports,indent=2)+'\n')
    return reports

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start',type=int,default=166)
    parser.add_argument('--stop',type=int,default=256)
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent/'conference_catalog')
    args=parser.parse_args()
    build(args.start,args.stop,args.directory)
