#!/usr/bin/env python3
"""Reproducible exact-arithmetic regression checks (not formal verification)."""
from __future__ import annotations
import argparse, copy, json, sys, time, unittest
from fractions import Fraction as F
from pathlib import Path
from exact_baseline import matrix, transpose, matmul, eye
from sos_obstruction import (make_instance,verify_certificate,rational_json,
                            rational_contact,dot,pd_pivots)
from rigidity import certificate,bernstein_coefficients
from projective_recovery import (demo,rational_square_root,reconstruct_value,
                                FacetValueOracle,recover_from_values,strong_probe_observer)
from padding import padded_instance
import sympy as s

ROOT=Path(__file__).resolve().parents[1]
FULL='--full' in sys.argv


def frozen(name): return json.loads((ROOT/'certificates'/name).read_text())


class ExactChecks(unittest.TestCase):
    def test_rational_circle_parameterization(self):
        for k in range(1,40):
            q=rational_contact(F(k,k+41))
            self.assertEqual(sum(q),1); self.assertEqual(dot(q,q),1)

    def test_degree_two_small_certificate(self):
        data=make_instance(2,F(1,2**32),F(1,2**40))
        result=verify_certificate(data)
        self.assertEqual(result['localizing_matrices_checked'],16)

    def test_degree_four_frozen_certificate(self):
        result=verify_certificate(frozen('sos_degree4_strong.json'))
        self.assertEqual(result['localizing_matrices_checked'],256)
        self.assertLess(result['functional_target_value'],0)

    def test_degree_six_frozen_certificate(self):
        result=verify_certificate(frozen('sos_degree6_strong.json'))
        self.assertEqual(result['localizing_matrices_checked'],4096)

    @unittest.skipUnless(FULL,'Use --full for the degree-eight exhaustive exact check.')
    def test_degree_eight_frozen_certificate(self):
        result=verify_certificate(frozen('sos_degree8_strong.json'))
        self.assertEqual(result['localizing_matrices_checked'],65536)

    def test_weak_limit_certificate(self):
        result=verify_certificate(make_instance(4,F(1,2**32),F(0)))
        self.assertEqual(result['ssc_convention'],'weak')

    def test_reject_changed_evaluation_point(self):
        data=frozen('sos_degree4_strong.json'); data['evaluation_points'][0][0]='7/3'
        with self.assertRaises(ValueError): verify_certificate(data)

    def test_reject_changed_input(self):
        data=frozen('sos_degree4_strong.json'); data['H'][0][0]='1/11'
        with self.assertRaises(ValueError): verify_certificate(data)

    def test_reject_changed_weight(self):
        data=frozen('sos_degree4_strong.json'); data['weights'][0]='1/10'
        with self.assertRaises(ValueError): verify_certificate(data)

    def test_reject_float_parameter(self):
        data=frozen('sos_degree4_strong.json'); data['epsilon']=0.125
        with self.assertRaises(ValueError): verify_certificate(data)

    def test_reject_nonpositive_expansion(self):
        with self.assertRaises(ValueError): make_instance(4,F(0),F(1,4))

    def test_exact_positive_definite_verifier(self):
        self.assertEqual(pd_pivots(matrix([[2,1],[1,2]])),[F(2),F(3,2)])
        with self.assertRaises(ValueError): pd_pivots(matrix([[1,2],[2,1]]))
        with self.assertRaises(ValueError): pd_pivots(matrix([[1,2],[0,1]]))

    def test_rigidity_frozen_interval_certificate(self):
        result=certificate()
        self.assertEqual(result,frozen('weak_rigidity.json'))
        self.assertEqual(len(result['triples']),20)
        self.assertEqual(sum(v['classification']=='strictly_worse' for v in result['triples']),5)

    def test_rigidity_certificate_corruption_detectable(self):
        original=certificate(); altered=copy.deepcopy(original)
        altered['positive_weights'][0]+=1
        self.assertNotEqual(original,altered)

    def test_bernstein_representation_identity(self):
        t,x=s.symbols('t x'); p=t**4+2*t**2+3
        bc=bernstein_coefficients(p,t,-s.Rational(1,3),s.Rational(2,3))
        expansion=sum(bc[j]*s.binomial(4,j)*x**j*(1-x)**(4-j) for j in range(5))
        self.assertEqual(s.expand(expansion-p.subs(t,x-s.Rational(1,3))),0)

    def test_rational_square_root(self):
        self.assertEqual(rational_square_root(F(49,121)),F(7,11))
        self.assertEqual(rational_square_root(F(0)),0)
        with self.assertRaises(ValueError): rational_square_root(F(2))
        with self.assertRaises(ValueError): rational_square_root(F(-1))

    def test_exact_decision_to_value_including_equality(self):
        for bits in (2,5,10):
            qs=[F(0),F(1),F(2**bits),F(1,2**bits),F(2**bits-1,2**bits)]
            for mu in qs:
                self.assertEqual(reconstruct_value(lambda tau:mu<=tau,bits),mu)

    def test_rank_three_projective_recovery(self):
        result=rational_json(demo(3))
        self.assertEqual(result,frozen('projective_rank3.json'))
        self.assertEqual(result['exact_value_queries'],24)

    def test_rank_four_projective_recovery(self):
        result=rational_json(demo(4))
        self.assertEqual(result,frozen('projective_rank4.json'))
        self.assertEqual(result['exact_value_queries'],73)
        self.assertEqual(result['isolating_k'],2)

    def test_rank_two_projective_recovery(self):
        T=matrix([[2,-1],[-1,2]]); Y=T; delta=F(1,1024)
        oracle=FacetValueOracle(Y,delta,strong_probe_observer(T))
        result=recover_from_values(Y,delta,oracle)
        self.assertEqual(sorted(map(tuple,transpose(result['T']))),sorted(map(tuple,transpose(T))))

    def test_recovery_rejects_nonsquare_value_ratio(self):
        Y=eye(2)
        def bad(v): return F(1) if not any(v) else F(2)
        with self.assertRaises(ValueError): recover_from_values(Y,F(1,1024),bad)

    def test_strong_probe_check_rejects_weak_contacts(self):
        H=matrix(frozen('weak_rigidity.json')['H'])
        check=strong_probe_observer(eye(3))
        oracle=FacetValueOracle(H,F(1,1024),check)
        with self.assertRaises(ValueError): oracle([0,0,0])

    def test_padded_frozen_instances_and_restriction(self):
        for D in (4,6,8):
            result=padded_instance(frozen(f'sos_degree{D}_strong.json'))
            self.assertEqual(rational_json(result),frozen(f'padded_degree{D}.json'))
            H=matrix(result['H']); base=matrix(frozen(f'sos_degree{D}_strong.json')['H'])
            q=[F(-1,3),F(2,3),F(2,3)]+[F(0)]*(result['rank']-3)
            self.assertEqual([dot(q,col) for col in transpose(H)][:len(base[0])],
                             [dot(q[:3],col) for col in transpose(base)])
            self.assertEqual(1-dot(q,q),1-dot(q[:3],q[:3]))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full',action='store_true')
    parser.add_argument('--report',type=Path,default=ROOT/'verification'/'test_report.json')
    args=parser.parse_args(); start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ExactChecks))
    report={'tests_run':result.testsRun,'failures':len(result.failures),
            'errors':len(result.errors),'skipped':len(result.skipped),
            'full_degree_eight_check':args.full,'successful':result.wasSuccessful(),
            'elapsed_seconds':round(time.monotonic()-start,3),
            'assurance':'Exact arithmetic computational checks; not independent review or proof-assistant verification.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    raise SystemExit(0 if result.wasSuccessful() else 1)

if __name__=='__main__': main()
