"""Export the explicit integer counterexample A=R R^T.

A_integer.mtx.gz is gzip-compressed Matrix Market coordinate/integer/symmetric
text. Entries are arbitrary-precision decimal integers; do not load through a
floating-point or fixed-width-integer reader. Only the lower triangle is stored.
"""
from pathlib import Path
import gzip,json,csv,time

HERE=Path(__file__).resolve().parent.parent/'data'

def export_matrix():
    start=time.monotonic()
    d=json.loads((HERE/'facets.json').read_text())
    R=d['facet_normals'];n=len(R)
    assert n==444 and all(len(row)==7 for row in R)
    with (HERE/'R_integer.csv').open('w',newline='') as f:
        w=csv.writer(f,lineterminator='\n');w.writerows(R)
    raw=(HERE/'A_integer.mtx.gz').open('wb')
    with raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as g:
        def line(s):g.write((s+'\n').encode('ascii'))
        line('%%MatrixMarket matrix coordinate integer symmetric')
        line('% Exact PF-03 counterexample; A = R_integer.csv times its transpose.')
        line('% All integers are arbitrary precision. Lower triangle, including diagonal.')
        line(f'{n} {n} {n*(n+1)//2}')
        positive=True;max_digits=0;minimum=None
        for i,row in enumerate(R):
            for j in range(i+1):
                value=sum(x*y for x,y in zip(row,R[j]))
                assert value>0
                max_digits=max(max_digits,len(str(value)))
                minimum=value if minimum is None else min(minimum,value)
                line(f'{i+1} {j+1} {value}')
    info={'order':n,'rank':7,'real_cp_rank':7,'entry_type':'strictly positive integers',
          'rational_nonnegative_factor':'does not exist at any finite width; see proof',
          'matrix_definition':'A = R R^T, R = R_integer.csv',
          'nonnegative_real_factor':'B = R O, O = orthogonal_matrix in exact_algebraic_certificate.json',
          'stored_triangle_entries':n*(n+1)//2,'max_entry_decimal_digits':max_digits,
          'compressed_matrix_bytes':(HERE/'A_integer.mtx.gz').stat().st_size}
    (HERE/'matrix_metadata.json').write_text(json.dumps(info,indent=2))
    print(json.dumps(info,indent=2));print('Export seconds:',round(time.monotonic()-start,3))
    return info

if __name__=='__main__':
    export_matrix()
