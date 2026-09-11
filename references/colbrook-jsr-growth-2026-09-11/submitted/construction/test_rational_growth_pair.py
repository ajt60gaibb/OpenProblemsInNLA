"""Exact unit tests for the optional rational construction interface."""
from fractions import Fraction as F
import unittest
from rational_growth_pair import construct, fractional_pair, jordan_at_one, kronecker


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


class ConstructionTests(unittest.TestCase):
    def test_half(self):
        result = construct(F(1, 2))
        self.assertEqual(result['dimension'], 6)
        a = [[F(x) for x in row] for row in result['A']]
        p = [[F(x) for x in row] for row in result['P_or_zero']]
        self.assertEqual(a[1][1], F(1, 4))
        self.assertEqual(a[3][3], F(1, 2))
        self.assertEqual(matmul(p, p), p)
        u = [[F(x) for x in row] for row in [[1,-1,0,1,0,0],[0,0,0,0,0,1]]]
        v = [[F(x) for x in row] for row in [[1,0],[0,0],[1,0],[0,0],[0,1],[0,1]]]
        aq = [[F(int(i == j)) for j in range(6)] for i in range(6)]
        for q in range(12):
            self.assertEqual(matmul(matmul(u, aq), v),
                             [[1-q*F(1,4)**q, q*F(1,2)**q], [F(0),F(1)]])
            aq = matmul(aq, a)

    def test_integer_and_zero(self):
        for m in range(6):
            result = construct(F(m))
            self.assertEqual(result['dimension'], m+1)
            self.assertEqual(result['A'], [[str(x) for x in row] for row in jordan_at_one(m+1)])
            self.assertTrue(all(x == '0' for row in result['P_or_zero'] for x in row))
            self.assertNotEqual(result['A'], result['P_or_zero'])

    def test_seven_thirds(self):
        result = construct(F(7, 3))
        self.assertEqual(result['dimension'], 18)
        base_a, base_p = fractional_pair(F(1,8), F(1,4))
        j = jordan_at_one(3)
        for key, base in [('A', base_a), ('P_or_zero', base_p)]:
            expected = kronecker(base, j)
            self.assertEqual(result[key], [[str(x) for x in row] for row in expected])

    def test_exact_dyadic_entries(self):
        for b in range(2, 12):
            for a in range(1, b):
                result = construct(F(a,b))
                for key in ('A', 'P_or_zero'):
                    for row in result[key]:
                        for text in row:
                            denominator = F(text).denominator
                            self.assertEqual(denominator & (denominator - 1), 0)

    def test_rational_pair_irrational_exponent(self):
        a, p = fractional_pair(F(1,4), F(1,3))
        self.assertEqual(a[3][3], F(1,3))
        self.assertEqual(matmul(p,p), p)

    def test_invalid_parameters_and_resource_limits(self):
        for gamma in (F(-1), F(-1,100)):
            with self.assertRaises(ValueError):
                construct(gamma)
        with self.assertRaises(TypeError):
            construct(0.5)
        with self.assertRaises(ValueError):
            construct(F(1000))
        with self.assertRaises(ValueError):
            construct(F(1,1001))
        for lam, mu in [(F(1,2),F(3,4)),(F(0),F(1,2)),(F(1,4),F(1,4)),(F(1,4),F(1))]:
            with self.assertRaises(ValueError):
                fractional_pair(lam,mu)
        with self.assertRaises(ValueError):
            kronecker([], [[F(1)]])


if __name__ == '__main__':
    unittest.main(verbosity=2)
