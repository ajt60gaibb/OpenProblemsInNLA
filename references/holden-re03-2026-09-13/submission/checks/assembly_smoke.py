#!/usr/bin/env python3
"""New assembly smoke checks, not the unavailable continuation proof/test suite."""
from __future__ import annotations
import argparse
import json
import platform
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from hodlr import is_hodlr, project_hodlr
from two_stage import (TwoStageParameters, approximate_two_stage,
                       two_stage_with_parameters)


class OpaqueOracle:
    """Exercise the dimension-and-vector-product interface without a matrix field."""
    def __init__(self, a: np.ndarray) -> None:
        self._apply = lambda v, transpose: (a.T if transpose else a) @ v
        self.n = a.shape[0]
        self.queries = 0

    def matvec(self, v: np.ndarray, transpose: bool = False) -> np.ndarray:
        if v.shape != (self.n,):
            raise ValueError('Expected one query vector')
        self.queries += 1
        return self._apply(v, transpose)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'rerun_results/assembly_smoke.json')
    args = parser.parse_args()
    rng = np.random.default_rng(20260913)
    records = []
    cases = [(16, 1, 0.2), (32, 2, 0.1), (16, 1, 1e-300),
             (16, 1, float(np.nextafter(0.0, 1.0)))]
    for n, k, epsilon in cases:
        a = rng.standard_normal((n, n))
        oracle = OpaqueOracle(a)
        result = approximate_two_stage(oracle, k, epsilon, rng)
        reference = project_hodlr(a, k)
        require(result.method == 'n_query_baseline', 'Unexpected fallback method')
        require(result.queries == oracle.queries == n, 'Query count mismatch')
        require(is_hodlr(result.matrix, k), 'Output is not proper HODLR')
        require(np.allclose(result.matrix, reference, rtol=1e-10, atol=1e-10),
                'Fallback differs from full-data projection')
        records.append({'kind': 'baseline', 'n': n, 'k': k,
                        'epsilon': epsilon, 'queries': result.queries,
                        'passed': True})
    n, k = 32, 1
    a = np.diag(rng.uniform(0.5, 1.5, n))
    oracle = OpaqueOracle(a)
    parameters = TwoStageParameters(4, 8, 2, 32)
    result = two_stage_with_parameters(oracle, k, parameters, rng)
    error = float(np.linalg.norm(a - result.matrix) / np.linalg.norm(a))
    require(result.method == 'two_stage_shared_regression', 'Sketch path not used')
    require(result.queries == oracle.queries, 'Sketch query count mismatch')
    require(result.queries <= result.budget, 'Sketch exceeded stated budget')
    require(is_hodlr(result.matrix, k), 'Sketch output is not proper HODLR')
    require(error < 1e-10, 'Diagonal exact-instance smoke check failed')
    records.append({'kind': 'experimental_diagonal', 'n': n, 'k': k,
                    'queries': result.queries, 'budget': result.budget,
                    'relative_error': error, 'passed': True,
                    'scope': 'Experimental widths on one exact instance; no uniform guarantee'})
    report = {'check_type': 'new_assembly_smoke', 'seed': 20260913,
              'python': platform.python_version(), 'numpy': np.__version__,
              'original_continuation_suite_reproduced': False,
              'formal_proof_verification': False,
              'records': records, 'all_checks_passed': True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f'Assembly smoke checks passed: {len(records)} cases. Report: {args.output}')
    print('These checks do not verify the mathematical proofs or replace missing suites.')


if __name__ == '__main__':
    main()
