from pathlib import Path
import json,sys
import sympy as s
R=Path(__file__).resolve().parents[1];sys.path.insert(0,str(R/'code'))
out=R/'writeup/pencil_audit.tex';parts=[];p=R/'data/interrupted_pencil.json'
status={'status':'NOT_PROMOTED','reason':'No successfully extracted pencil'}
if p.exists():
    data=json.loads(p.read_text());xs=s.symbols('x0:5');Bs=[s.Matrix([[s.Rational(v) for v in row] for row in B]) for B in data['basis']]
    A=sum((x*B for x,B in zip(xs,Bs)),s.zeros(4));cert=None
    try:
        from sos_pencil_certificate import verify
        for candidate in sorted((R/'data').glob('pencil_sos_degree_*.json')):
            if candidate.stem.endswith('_verified'):continue
            try:res=verify(candidate);cert=(candidate,res);break
            except Exception:pass
    except Exception:pass
    charts=[]
    for i in range(5):
        c=R/f'data/pencil_chart_{i}.json'
        charts.append(json.loads(c.read_text()) if c.exists() else None)
    chart_pass=all(c is not None and c.get('certified_no_real_points') for c in charts)
    if cert or chart_pass:
        status={'status':'CERTIFIED','method':'rational positive Gram form' if cert else 'projective charts and rational Hermite forms'}
        parts += [r'\subsection{A certified pencil from the interrupted continuation}',
          r'The preserved five-parameter rational pencil was extracted and checked separately. With new coordinate names, it is',
          r'\[\resizebox{0.98\linewidth}{!}{$A(x)='+s.latex(A)+r'.$}\]',
          r'The five coefficient matrices are linearly independent over $\Q$.']
        if cert:
            path,res=cert;status['certificate']=str(path.relative_to(R));status['degree']=res['degree'];status['gram_dimension']=res['gram_dimension']
            parts += [r'The positive Gram certificate has polynomial degree '+str(res['degree'])+r' and Gram dimension '+str(res['gram_dimension'])+r'. Its complete rational data are in \path{'+str(path.relative_to(R))+r'}.',
              r'Exact coefficient comparison verifies identity~\eqref{sos}, and rational elimination verifies every positive-definiteness pivot. Thus all $3\times3$ minors can vanish simultaneously only at $x=0$.']
        else:
            parts += [r'Each of the five projective charts is exactly certified empty. The trace-form signatures, or unit-ideal outcomes, are recorded in the five \path{data/pencil_chart_*.json} files. The projective-chart argument therefore proves that all nonzero real members have rank at least three.']
        parts += [r'An orthogonal-complement basis gives eleven measurements. Combined with the rank-one lower bound at $d=4$, this independently verifies $\mu_\R(4,1)=11$. This is a replacement certificate for an already established value, not a new value of $\mu_\R$.']
        W=s.Matrix.hstack(*[s.Matrix(list(B)) for B in Bs]).T.nullspace()
        assert len(W)==11
        (R/'data/interrupted_pencil_measurements.json').write_text(json.dumps({'d':4,'r':1,'rows':[[str(v) for v in w] for w in W], 'kernel_basis':data['basis']},indent=2))
    else:
        status={'status':'NOT_PROMOTED','reason':'The completed finite certificate checks were inconclusive or did not pass','chart_statuses':[None if c is None else c.get('certified_no_real_points') for c in charts]}
        parts += [r'\subsection{Status of the preserved small-pencil calculation}',
          r'The interrupted continuation included a proposed simpler $4\times4$ pencil. The completed checks in this archive did not supply a complete accepted certificate for that pencil, so it is not used as a theorem here. The extracted rational data and the exact outcomes are retained for audit. This does not retract the earlier independently certified Xu construction, and an inconclusive chart calculation is not a counterexample.']
else:
    parts += [r'\subsection{Status of the preserved small-pencil calculation}',r'No new small-pencil certificate is asserted in this continuation. The earlier Xu certificate remains available in the preserved prior archive.']
(R/'data/pencil_audit_status.json').write_text(json.dumps(status,indent=2));out.write_text('\n\n'.join(parts)+'\n');print(json.dumps(status,indent=2))
