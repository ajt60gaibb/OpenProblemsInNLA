#!/usr/bin/env python3
"""Audit selected printed constants against freshly computed exact quantities."""
from pathlib import Path
from checks import ie17

def main():
    if not __debug__: raise RuntimeError('Run without -O: checks use assertions.')
    r=ie17()
    tex=(Path(__file__).resolve().parents[1]/'proofs'/'IE-17.tex').read_text()
    keys=['upper_row_quadratic','upper_column_quadratic']
    for key in keys:
        q=r[key]
        token=r'\frac{'+str(q.numerator)+'}{'+str(q.denominator)+'}'
        assert token in tex, (key,token)
    for q in r['tilde_squared']:
        token=r'\frac{'+str(q.numerator)+'}{'+str(q.denominator)+'}'
        assert token in tex,token
    for q in r['lower_principal_minors']: assert str(q) in tex
    assert '2715630211217370564' not in tex
    print('Selected LSMR manuscript constants: PASS')
    print('This is a transcription audit, not a proof assistant.')

if __name__=='__main__': main()
