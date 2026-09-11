"""Independent exact checks. Does not import or execute submission Python code.

Ryser inclusion-exclusion with Gray-code column sums is deliberately different
from the supplied subset-DP and C++ polarization/derivative algorithms.
"""
from pathlib import Path
import argparse, itertools, json, math, random, subprocess, tempfile, time

OUT = Path(__file__).resolve().parent
PKG = OUT.parent / 'pr-89/references/colbrook-arithmetic-2026-09-11/submitted/NLA_partial_results_submission_package'
VERIFIER = OUT/'build/verify_permanent'

def ryser(a):
    n = len(a)
    sums = [0] * n
    old = 0
    total = 0
    for k in range(1, 1 << n):
        gray = k ^ (k >> 1)
        flip = gray ^ old
        j = flip.bit_length() - 1
        direction = 1 if gray & flip else -1
        product = 1
        for i in range(n):
            sums[i] += direction * a[i][j]
            product *= sums[i]
        total += (-1 if (n + gray.bit_count()) % 2 else 1) * product
        old = gray
    return total

def brute(a):
    n = len(a)
    return sum(math.prod(a[i][p[i]] for i in range(n))
               for p in itertools.permutations(range(n)))

def parse_witnesses(path, n):
    result = {}
    for line in path.read_text().splitlines():
        cells = line.split()
        if not cells:
            continue
        value = int(cells[0])
        assert value not in result, (path, 'duplicate')
        assert len(cells) == n + 1
        assert all(len(row) == n and set(row) <= {'+', '-'} for row in cells[1:])
        result[value] = [[1 if c == '+' else -1 for c in row] for row in cells[1:]]
    return result

def call_verifier(a, claim, threads=1):
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / 'matrix.txt'
        path.write_text(f'{len(a)} {claim}\n' + ''.join(' '.join(map(str,r))+'\n' for r in a))
        return subprocess.run([str(VERIFIER), str(path), str(threads)],
                              capture_output=True, text=True)

def main():
    global OUT, PKG, VERIFIER
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=PKG)
    parser.add_argument('--verifier', type=Path, default=VERIFIER)
    parser.add_argument('--out', type=Path, default=OUT)
    args = parser.parse_args()
    OUT, PKG, VERIFIER = args.out.resolve(), args.package.resolve(), args.verifier.resolve()
    OUT.mkdir(parents=True, exist_ok=True)
    began = time.monotonic()
    report = {'algorithm': 'exact integer Ryser Gray-code inclusion-exclusion', 'witness_catalogs': []}
    count = 0
    for name in [f'{f}{n}' for n in range(1,11) for f in ('u','o')] + ['c8','f7']:
        n = int(name[1:])
        data = parse_witnesses(PKG/f'data/ac12/{name}_witnesses.txt', n)
        values = set(map(int,(PKG/f'data/ac12/{name}_spectrum.txt').read_text().split()))
        assert set(data) == values
        assert values == set(map(int,(PKG/f'data/ac12/u{n}_spectrum.txt').read_text().split()))
        for value, a in data.items():
            assert abs(ryser(a)) == value, (name, value)
            if name.startswith('u'):
                assert all(a[i][j] == 1 for i in range(n) for j in range(i))
            count += 1
        report['witness_catalogs'].append({'name':name, 'count':len(data)})
        print('PASS Ryser witnesses', name, len(data), flush=True)
    assert count == 5528
    report['all_witnesses'] = count
    report['independent_exhaustive_normalized_spectra'] = []
    # All normalized matrices, without row/column permutation reductions or pruning.
    # Normalizing first row/column by signs preserves absolute permanent.
    for n in range(1,6):
        found = set()
        for core in range(1 << ((n-1)**2)):
            a = [[1]*n for _ in range(n)]
            for i in range(1,n):
                for j in range(1,n):
                    a[i][j] = -1 if (core >> ((i-1)*(n-1)+j-1)) & 1 else 1
            val = ryser(a)
            if n <= 4:
                assert val == brute(a)
            found.add(abs(val))
        wanted = set(map(int,(PKG/f'data/ac12/u{n}_spectrum.txt').read_text().split()))
        assert found == wanted, n
        report['independent_exhaustive_normalized_spectra'].append(
            {'n':n,'matrices':1 << ((n-1)**2),'absolute_values':sorted(found),
             'every_matrix_direct_permutation_checked': n <= 4})
        print('PASS unreduced normalized exhaustive spectrum', n, flush=True)
    rng = random.Random(890611)
    checks = wrong = negative = 0
    for n in range(1,9):
        matrices = [[[1]*n for _ in range(n)], [[-1]*n for _ in range(n)]]
        matrices += [[[rng.choice((-1,1)) for _ in range(n)] for _ in range(n)] for _ in range(16)]
        for j,a in enumerate(matrices):
            val = ryser(a)
            if n <= 7:
                assert brute(a) == val
            result = call_verifier(a, val, 1+j%5)
            assert result.returncode == 0, (n, val, result.stdout, result.stderr)
            checks += 1
            negative += val < 0
            for bad in (val+2, val-2):
                result = call_verifier(a,bad,1+j%3)
                assert result.returncode != 0, ('accepted wrong value', n, val, bad)
                wrong += 1
    report.update(full_verifier_crosschecks=checks, negative_permanent_crosschecks=negative,
                  wrong_claim_rejections=wrong)
    # In particular test syntax/shape/domain validation, independently of assertion harness.
    malformed = ['0 1\n', '2 2\n1 1\n1 0\n', '2 2\n1 1\n1\n',
                 '2 2\n1 1\n1 1\n9\n', '2 1\n1 1\n1 1\n', '41 2\n']
    with tempfile.TemporaryDirectory() as d:
        p = Path(d)/'bad.txt'
        for bad in malformed:
            p.write_text(bad)
            r = subprocess.run([str(VERIFIER),str(p)],capture_output=True,text=True)
            assert r.returncode != 0, bad
    report['malformed_input_rejections'] = len(malformed)
    report['small_ac11_Ryser'] = []
    for n in range(1,15):
        vals = list(map(int,(PKG/f'data/ac11/min{n}.txt').read_text().split()))
        assert vals[0] == n and len(vals) == n*n+2
        a = [vals[2+i*n:2+(i+1)*n] for i in range(n)]
        q = 1 << (n - ((n+1).bit_length()-1))
        assert vals[1] == q == ryser(a)
        report['small_ac11_Ryser'].append(n)
    report['seconds'] = time.monotonic()-began
    (OUT/'independent-permanent-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('ALL INDEPENDENT CHECKS PASS', json.dumps(report), flush=True)

if __name__ == '__main__':
    main()
