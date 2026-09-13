"""Implementation tests; they do not establish the quantified research claims."""
import unittest
import numpy as np
import sympy as sp
from rational_hankel import recover, represented_slices
from verify_exact import positive_definite_exact
from mixed_als_previous import represented, mixed_update, cycle_schedule


class RoundFiveTests(unittest.TestCase):
    def test_rank_validation(self):
        with self.assertRaises(ValueError): recover([sp.eye(1)],0)

    def test_shape_validation(self):
        with self.assertRaises(ValueError): recover([sp.eye(2)],1)

    def test_exact_entry_validation(self):
        with self.assertRaises(ValueError): recover([sp.Matrix([[sp.Float('1.2')]])],1)

    def test_singular_input_fails_explicitly(self):
        result=recover([sp.zeros(2),sp.zeros(2)],2)
        self.assertFalse(result.success)
        self.assertIn('singular',result.reason)

    def test_rank_one_exact(self):
        a=sp.Matrix([1,2]); b=sp.Matrix([3,4]); c=sp.Matrix([5,7])
        t=represented_slices(a,b,c); result=recover(t,1,seed=7)
        self.assertTrue(result.success)
        self.assertEqual(represented_slices(result.x,result.y,result.z),t)

    def test_rank_three_exact(self):
        a=sp.Matrix([[1,1,1],[0,1,2],[0,0,1]])
        b=sp.Matrix([[1,2,0],[0,1,2],[0,0,1]])
        c=sp.Matrix([[1,1,1],[1,2,3],[1,4,9]])
        t=represented_slices(a,b,c); result=recover(t,3,seed=11)
        self.assertTrue(result.success)
        self.assertEqual(result.x.cols,5)
        self.assertEqual(represented_slices(result.x,result.y,result.z),t)
        self.assertEqual(result.grid_size & (result.grid_size-1),0)

    def test_seed_reproducibility(self):
        t=represented_slices(sp.eye(2),sp.eye(2),sp.Matrix([[1,2],[2,3]]))
        a,b=recover(t,2,seed=5),recover(t,2,seed=5)
        self.assertTrue(a.success)
        self.assertEqual((a.x,a.y,a.z),(b.x,b.y,b.z))

    def test_positive_definite_certificate(self):
        self.assertTrue(positive_definite_exact(sp.Matrix([[2,1],[1,2]])))
        self.assertFalse(positive_definite_exact(sp.Matrix([[1,2],[2,1]])))
        self.assertFalse(positive_definite_exact(sp.zeros(2)))

    def test_binary_schedule(self):
        for r in range(2,20):
            seq=cycle_schedule(r)
            self.assertEqual(len(seq),1+2*((r-1).bit_length()))
            for i in range(r):
                for j in range(r):
                    if i!=j:
                        self.assertTrue(any(a[i]==1 and a[j]==2 for a in seq))

    def test_mixed_block_monotonicity(self):
        rng=np.random.default_rng(73)
        true=[rng.normal(size=(3,2)) for _ in range(3)]
        target=represented(true)
        f=[rng.normal(size=(3,2)) for _ in range(3)]
        for selection in ([0,0],[1,2],[2,1]):
            old=np.linalg.norm(represented(f)-target)
            new=mixed_update(target,f,selection)
            self.assertLessEqual(np.linalg.norm(represented(new)-target),old+1e-10)
            f=new

    def test_zero_residual_fixed_point(self):
        true=[np.array([[1.,1.],[0.,.2]]),np.eye(2),np.eye(2)]
        target=represented(true)
        f=true
        for selection in cycle_schedule(2): f=mixed_update(target,f,selection)
        self.assertLess(np.linalg.norm(represented(f)-target),1e-12)

    def test_mixed_validation(self):
        with self.assertRaises(ValueError): cycle_schedule(0)
        with self.assertRaises(ValueError): mixed_update(np.zeros((2,2,2)),[np.ones((2,2))]*3,[0,3])


if __name__=='__main__': unittest.main(verbosity=2)
