"""Unit and corruption tests for the exact verifier's arithmetic primitives."""
from pathlib import Path
from fractions import Fraction as F
import json,random,tempfile,unittest
from field3 import *
from exact_facets import null_normal,primitive
from verify_seed import verify_seed

DATA=Path(__file__).resolve().parent.parent/'data'

class FieldTests(unittest.TestCase):
    def test_defining_relation(self):
        self.assertEqual(ALPHA**3,E(2))
    def test_reduction_of_higher_powers(self):
        self.assertEqual(ALPHA**7,E(0,4,0))
    def test_inverse(self):
        for i in range(1,15):
            x=E(F(i,7),F(3-i,5),F(i+1,11))
            self.assertEqual(x*x.inverse(),ONE)
    def test_zero_inverse_rejected(self):
        with self.assertRaises(ZeroDivisionError):ZERO.inverse()
    def test_distributivity(self):
        rng=random.Random(934)
        for _ in range(20):
            x,y,z=[E(*(rng.randrange(-5,6) for _ in range(3))) for k in range(3)]
            self.assertEqual(x*(y+z),x*y+x*z)
    def test_multiplication_independent_polynomial_reduction(self):
        x=E(F(3,7),F(-5,9),F(11,13));y=E(F(-2,5),F(7,11),F(5,17))
        p=[F(0)]*5
        for i,a in enumerate([x.c0,x.c1,x.c2]):
            for j,b in enumerate([y.c0,y.c1,y.c2]):p[i+j]+=a*b
        p[1]+=2*p[4];p[0]+=2*p[3]
        self.assertEqual(x*y,E(*p[:3]))
    def test_isolation(self):
        l,u=isolate_alpha(40)
        self.assertLess(l**3,F(2));self.assertLess(F(2),u**3)
        self.assertEqual(u-l,F(1,10**40))
    def test_interval_signs(self):
        I=isolate_alpha()
        self.assertTrue(positive(ALPHA-1,I))
        self.assertTrue(positive(2-ALPHA,I))
        self.assertFalse(positive(1-ALPHA,I))
    def test_encode_decode(self):
        x=E(F(1,17),F(-99,8),F(0))
        self.assertEqual(E.decode(x.encode()),x)
    def test_field_inverse_matrix(self):
        A=[[ONE,ALPHA],[ALPHA**2,E(3)]]
        self.assertEqual(multiply(A,field_inverse(A)),identity(2))
    def test_rational_rank(self):
        self.assertEqual(rational_rank([[F(1),F(2),F(3)],[F(2),F(4),F(6)]]),1)

class IntegerNullspaceTests(unittest.TestCase):
    def test_simple(self):
        n=null_normal([[1,0,2],[0,1,3]])
        self.assertTrue(n==(-2,-3,1) or n==(2,3,-1))
    def test_row_pivot(self):
        n=null_normal([[0,2,3],[1,0,4]])
        self.assertTrue(n==(8,3,-2) or n==(-8,-3,2))
    def test_column_pivot(self):
        self.assertIn(null_normal([[0,1,0],[0,0,1]]),[(1,0,0),(-1,0,0)])
    def test_deficient(self):
        self.assertIsNone(null_normal([[1,2,3],[2,4,6]]))
    def test_gcd_normalization(self):
        self.assertEqual(primitive([12,-18,30]),(2,-3,5))

class CertificateCorruptionTests(unittest.TestCase):
    def test_changed_orthogonal_entry_rejected(self):
        d=json.loads((DATA/'exact_algebraic_certificate.json').read_text())
        d['orthogonal_matrix'][0][0][0]=str(F(d['orthogonal_matrix'][0][0][0])+1)
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'bad.json';p.write_text(json.dumps(d))
            with self.assertRaises(AssertionError):verify_seed(p,False)
    def test_changed_local_gram_entry_rejected(self):
        d=json.loads((DATA/'exact_algebraic_certificate.json').read_text())
        d['restricted_gram'][0][0][0][0]=str(F(d['restricted_gram'][0][0][0][0])-1)
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'bad.json';p.write_text(json.dumps(d))
            with self.assertRaises(AssertionError):verify_seed(p,False)

if __name__=='__main__':
    unittest.main(verbosity=2)
