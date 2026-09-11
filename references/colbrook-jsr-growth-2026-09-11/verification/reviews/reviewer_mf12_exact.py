"""Independent Fraction checks of MF-12; no submission imports."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0)) for col in zip(*b)] for row in a]


def power(a, n):
    out = identity(len(a))
    while n:
        if n % 2:
            out = multiply(out, a)
        a = multiply(a, a)
        n //= 2
    return out


def pair(lam, mu):
    a = [[F(0) for _ in range(6)] for _ in range(6)]
    for i, value in enumerate((F(1), lam, lam, mu, mu, F(1))):
        a[i][i] = value
    a[1][2], a[3][4] = lam, mu
    u = [[F(x) for x in row] for row in ((1,-1,0,1,0,0),(0,0,0,0,0,1))]
    v = [[F(x) for x in row] for row in ((1,0),(0,0),(1,0),(0,0),(0,1),(0,1))]
    return a, multiply(v, u), u, v


def main():
    compressed_checks = 0
    for lam, mu in ((F(1,4),F(1,2)),(F(1,8),F(1,4)),(F(1,8),F(1,2)),(F(1,4),F(1,3))):
        a, p, u, v = pair(lam, mu)
        assert multiply(u, v) == identity(2)
        assert multiply(p, p) == p
        for q in range(11):
            assert multiply(multiply(u, power(a,q)), v) == [[1-q*lam**q,q*mu**q],[F(0),F(1)]]
            compressed_checks += 1

    budgets = 0
    for numerator, denominator in ((1,2),(1,3),(2,3),(1,4),(3,4),(9,10)):
        lam, mu = F(1,2**denominator), F(1,2**(denominator-numerator))
        for length in range(5):
            for gaps in product((0,1,2,5), repeat=length):
                a, z, mass = F(1), F(0), F(0)
                for q in gaps:
                    loss, gain = q*lam**q, q*mu**q
                    a, z = (1-loss)*a, (1-loss)*z+gain
                    mass = loss+(1-loss)*mass
                assert mass == 1-a and 0 <= mass <= 1
                assert z**denominator <= F(sum(gaps))**numerator
                budgets += 1

    lower_checks = 0
    for numerator, denominator in ((1,2),(1,3),(2,3)):
        lam, mu = F(1,2**denominator), F(1,2**(denominator-numerator))
        a, p, u, v = pair(lam, mu)
        for n in range(1,65):
            q = 0
            while lam**(-(q+1)) <= n:
                q += 1
            if q == 0:
                assert power(a,n)[0][0] == 1
            else:
                k, remainder = divmod(n,q+1)
                assert k*(q+1)+remainder == n
                loss, gain = q*lam**q, q*mu**q
                assert k*loss >= F(1,4)
                geometric = 1-(1-loss)**k
                assert geometric >= F(1,5)
                z = gain/loss*geometric
                word = multiply(power(a,remainder),power(multiply(p,power(a,q)),k))
                assert multiply(word,v)[0][1] == z
                assert (gain/loss)**denominator >= (lam*n)**numerator
            lower_checks += 1

    base = Path(__file__).resolve().parents[1]
    source = base/'nla_submission/MF-12/arbitrary_growth_exponents.tex'
    data = source.read_bytes().decode('utf-8').replace('\r\n','\n').encode('utf-8')
    result = {'status':'PASS','arithmetic':'stdlib Fraction; no submission imports',
              'source_bytes':len(data),'source_sha256':hashlib.sha256(data).hexdigest(),
              'compressed_power_checks':compressed_checks,'gap_budget_checks':budgets,
              'exact_length_lower_checks':lower_checks,
              'scope':'Finite exact identity checks. The all-exponent/all-length result is proved analytically.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
