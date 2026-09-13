from __future__ import annotations
from fractions import Fraction
import math
import unittest
import numpy as np
from scipy.integrate import quad
from scipy.special import digamma
from src.wishart_geometry import (
    orthonormalize, haar_frame, psd_inverse_sqrt, logdet_spd,
    sample_tilted_wishart, schur_components, kernel_graph, ridge_potential,
    angular_quantities, angular_bound, graph_coordinate_field,
    finite_accuracy_scale, SymmetricOracle, adaptive_frames,
)

class GeometryTests(unittest.TestCase):
    def setUp(self):
        self.rng = np.random.default_rng(87217)

    def test_01_haar_frame(self):
        u = haar_frame(17,4,self.rng)
        np.testing.assert_allclose(u.T@u,np.eye(4),atol=1e-12)

    def test_02_invalid_inputs(self):
        with self.assertRaises(ValueError): haar_frame(2,3,self.rng)
        with self.assertRaises(ValueError): sample_tilted_wishart(2,2,1,self.rng)
        with self.assertRaises(ValueError): sample_tilted_wishart(3,1,-1,self.rng)
        with self.assertRaises(ValueError): angular_bound(3,2,1,1)
        with self.assertRaises(ValueError): finite_accuracy_scale(8,2,0)
        with self.assertRaises(ValueError): finite_accuracy_scale(8,2,0.5)

    def test_03_inverse_square_root(self):
        a=self.rng.normal(size=(5,5));a=a@a.T+np.eye(5)
        b=psd_inverse_sqrt(a)
        np.testing.assert_allclose(b@a@b,np.eye(5),atol=2e-12)

    def test_04_sample_rank_and_kernel(self):
        h,u=sample_tilted_wishart(18,3,8,self.rng,scale=1/18)
        np.testing.assert_allclose(h@u,0,atol=3e-14)
        self.assertEqual(np.linalg.matrix_rank(h,tol=1e-10),15)
        self.assertGreater(np.linalg.eigvalsh(h)[3],0)

    def _example(self,n=14,k=3,t=4):
        h,u=sample_tilted_wishart(n,k,7,self.rng)
        v=haar_frame(n,t,self.rng)
        a,b,s,w=schur_components(h,v)
        _,qs=np.linalg.eigh(s)
        us=qs[:,:k]
        c,z,km=kernel_graph(a,b,us)
        return h,u,v,a,b,s,w,us,c,z,km

    def test_05_schur_reconstruction(self):
        h,u,v,a,b,s,w,us,c,z,km=self._example()
        q=np.column_stack([v,w])
        block=np.block([[a,b.T],[b,b@np.linalg.solve(a,b.T)+s]])
        np.testing.assert_allclose(q@block@q.T,h,atol=2e-12)

    def test_06_graph_is_kernel(self):
        h,u,v,a,b,s,w,us,c,z,km=self._example()
        q=np.column_stack([v,w])
        np.testing.assert_allclose(h@q@z,0,atol=2e-12)
        np.testing.assert_allclose(z.T@z,np.eye(3),atol=2e-12)

    def test_07_pseudodeterminant_identity(self):
        for n,k,t in [(8,1,2),(13,2,4),(20,4,6)]:
            h,u,v,a,b,s,w,us,c,z,km=self._example(n,k,t)
            lhs=np.log(np.linalg.eigvalsh(h)[k:]).sum()
            rhs=logdet_spd(a)+np.log(np.linalg.eigvalsh(s)[k:]).sum()+logdet_spd(np.eye(k)+c)
            self.assertAlmostEqual(lhs,rhs,places=10)

    def test_08_overlap_graph_identity(self):
        h,u,v,a,b,s,w,us,c,z,km=self._example()
        np.testing.assert_allclose(z[:v.shape[1]].T@z[:v.shape[1]],c@np.linalg.inv(np.eye(3)+c),atol=2e-12)

    def test_09_ridge_graph_identity(self):
        h,u,v,a,b,s,w,us,c,z,km=self._example()
        alpha=7/3
        lhs=ridge_potential(u,v,alpha)
        rhs=logdet_spd(np.eye(3)+(1+alpha)*c)-logdet_spd(np.eye(3)+c)
        self.assertAlmostEqual(lhs,rhs,places=11)

    def test_10_one_query_determinant_update(self):
        h,u,v,a,b,s,w,us,c,z,km=self._example()
        direction=self.rng.standard_normal(w.shape[1]);direction/=np.linalg.norm(direction)
        alpha=7/3;beta=1+alpha
        r=direction@us@np.linalg.solve(np.eye(3)+beta*c,us.T@direction)
        new=np.column_stack([v,w@direction])
        delta=ridge_potential(u,new,alpha)-ridge_potential(u,v,alpha)
        self.assertAlmostEqual(delta,math.log1p(alpha*r),places=10)
        self.assertLessEqual(delta,alpha*r+1e-12)

    def test_11_divergence_coordinate_derivative(self):
        for d,k in [(5,1),(8,2),(10,3)]:
            a=self.rng.normal(size=(d,d));km=a@a.T
            v=self.rng.normal(size=d);v/=np.linalg.norm(v)
            nu=7.;beta=1+nu/k;u=np.eye(d)[:,:k]
            exact=angular_quantities(u,km,v,beta,nu)[0]
            numerical=0.;step=1e-6
            for i in range(d-k):
                for j in range(k):
                    y=np.zeros((d-k,k));y[i,j]=step
                    numerical+=(graph_coordinate_field(y,km,v,beta)[i,j]-graph_coordinate_field(-y,km,v,beta)[i,j])/(2*step)
            self.assertAlmostEqual(exact,numerical,places=8)

    def test_12_log_density_derivative(self):
        d,k=9,3;nu=11.;beta=1+nu/k
        a=self.rng.normal(size=(d,d));km=a@a.T
        v=self.rng.normal(size=d);v/=np.linalg.norm(v);u=np.eye(d)[:,:k]
        f=np.linalg.inv(np.eye(k)+beta*u.T@km@u)
        direction=np.outer(v[k:],v[:k])@f
        def density(t):
            y=t*direction
            uy=np.vstack([np.eye(k),y])@psd_inverse_sqrt(np.eye(k)+y.T@y)
            return nu/2*logdet_spd(np.eye(k)+uy.T@km@uy)
        step=1e-6;fd=(density(step)-density(-step))/(2*step)
        self.assertAlmostEqual(fd,angular_quantities(u,km,v,beta,nu)[1],places=8)

    def test_13_pointwise_integration_bound(self):
        for _ in range(80):
            d,k=12,3;nu=30.;beta=1+nu/k
            u=haar_frame(d,k,self.rng)
            km=np.diag(np.exp(self.rng.uniform(-5,5,d)))
            v=np.eye(d)[:,int(self.rng.integers(d))]
            divergence,score,r=angular_quantities(u,km,v,beta,nu)
            self.assertLessEqual(divergence+score+(d-k)*r,k+r+nu/beta+1e-11)

    def test_14_rank_one_psd_domination(self):
        d,k=14,3;u=haar_frame(d,k,self.rng)
        spectrum=np.exp(self.rng.uniform(-4,4,d));km=np.diag(spectrum)
        c=u.T@km@u
        for j in range(d):
            a=u[j,:]
            self.assertGreaterEqual(np.linalg.eigvalsh(c-spectrum[j]*np.outer(a,a))[0],-1e-11)

    def test_15_scalar_resolvent_bound(self):
        for beta in [0.2,1,2,100]:
            for c in np.logspace(-10,10,1000):
                self.assertLessEqual(c/((1+beta*c)*(1+c)),1/beta)

    def test_16_angular_moment_by_quadrature(self):
        # A rank-one K permits one-dimensional beta integrals.  Quadrature is
        # a component check, not the proof of the general Grassmann inequality.
        for d,nu,kappa in [(5,0,2),(9,3,5),(16,20,40)]:
            beta=1+nu;exponent=nu/2
            def fun(h,which):
                weight=((1+kappa*h)/(1+kappa))**exponent
                if which==0: return weight
                if which==1: return weight*h/(1+beta*kappa*h)
                return weight*(1-h)/(d-1)/(1+beta*kappa*h)
            values=[quad(lambda x:fun(x,j),0,1,weight='alg',wvar=(-0.5,(d-3)/2),epsabs=1e-12)[0] for j in range(3)]
            observed=max(values[1]/values[0],values[2]/values[0])
            self.assertLessEqual(observed,angular_bound(d,1,nu,beta)+1e-9)

    def test_17_zero_K_moment(self):
        for d,k,nu in [(8,2,0),(20,3,4),(100,4,90)]:
            self.assertLessEqual(k/d,angular_bound(d,k,nu,1+nu/k))

    def test_18_mean_log_graph_telescope(self):
        # Exact finite sums for the nu=0 law; the k=1 case telescopes.
        for n,t in [(12,3),(50,9),(100,24)]:
            value=sum(digamma(j/2) for j in range(n-t+1,n+1))-sum(digamma(j/2) for j in range(n-1-t+1,n))
            self.assertAlmostEqual(value,digamma(n/2)-digamma((n-t)/2),places=11)

    def test_19_spectral_scale_algebra(self):
        for n,k,nu in [(100,2,20),(200,1,30),(1000,12,180)]:
            difference=math.sqrt(n+nu)-math.sqrt(n-k-1)
            self.assertGreaterEqual(difference,(nu+k)/(3*math.sqrt(n)))

    def test_20_cosine_hyperbolic_exact_constant(self):
        certificate=sum(Fraction(10**(2*j),math.factorial(2*j)) for j in range(1,8))
        self.assertEqual(certificate,Fraction(5860808350,567567))
        self.assertGreater(certificate,10000)
        self.assertLess(Fraction(9,2000),Fraction(1,200))

    def test_21_trace_to_kernel_implication(self):
        # gap g, postprocessing accuracy g/4 -> captured trace >= 799k/800.
        for g in [1e-8,0.001,0.1]:
            e=g/4
            self.assertAlmostEqual(1-e/(200*g),799/800)

    def test_22_concavity_chord(self):
        for alpha in [0.01,1,10,1000]:
            for p in np.linspace(0,1,100):
                self.assertGreaterEqual(math.log1p(alpha*p)+1e-14,p*math.log1p(alpha))

    def test_23_finite_scale_limits_and_cap(self):
        for n,k in [(20,1),(100,3),(200,100)]:
            for e in [1e-20,1e-8,0.1,0.49]:
                f=finite_accuracy_scale(n,k,e)
                self.assertLessEqual(f,n*(1+1e-12))
                y=n*math.sqrt(e)/k
                if y<=1: self.assertGreaterEqual(f,n*math.log(2)-1e-10)

    def test_24_resolved_moderate_accuracy(self):
        for x in [3,10,100,1e6]:
            s=1/math.sqrt(x)
            self.assertGreaterEqual(math.log1p(x*s),0.25*math.log(math.e*x))

    def test_25_maximum_unresolved_ratio(self):
        for x in [2,10,1e3,1e8]:
            ell=math.log(math.e*x)
            theoretical=ell/math.log1p(ell)
            for y in np.logspace(-6,math.log10(x),400):
                ratio=min(y,ell)/math.log1p(y)
                self.assertLessEqual(ratio,theoretical+1e-10)

    def test_26_constant_accuracy_covariance_event(self):
        # Chi-square Chernoff exponent, then a 1/4-net quadratic-form bound.
        m_over_n=4096
        exponent=math.log(9)-m_over_n/512
        self.assertLess(exponent,-5)
        self.assertLess(2*math.exp(2*exponent),0.001)
        self.assertEqual(Fraction(1,8)/(1-2*Fraction(1,4)),Fraction(1,4))
        self.assertEqual(1-Fraction(3,8)**2,Fraction(55,64))

    def test_27_oracle_count_and_orthogonality(self):
        h,_=sample_tilted_wishart(24,2,8,self.rng,scale=1/24)
        for strategy in ['random','krylov','reply_null']:
            oracle=SymmetricOracle(h)
            frames=adaptive_frames(oracle,5,strategy,self.rng)
            self.assertEqual(oracle.queries,5)
            self.assertEqual(len(frames),6)
            np.testing.assert_allclose(frames[-1].T@frames[-1],np.eye(5),atol=2e-12)
        with self.assertRaises(ValueError): SymmetricOracle(h).matvec(np.ones((24,2)))

    def test_28_graph_formula_for_adaptive_transcript(self):
        h,u=sample_tilted_wishart(28,3,15,self.rng,scale=1/28)
        for strategy in ['krylov','reply_null']:
            frames=adaptive_frames(SymmetricOracle(h),5,strategy,self.rng)
            v=frames[-1];a,b,s,w=schur_components(h,v)
            _,q=np.linalg.eigh(s);c,z,km=kernel_graph(a,b,q[:,:3])
            alpha=5.
            self.assertAlmostEqual(ridge_potential(u,v,alpha),logdet_spd(np.eye(3)+(1+alpha)*c)-logdet_spd(np.eye(3)+c),places=9)

if __name__=='__main__': unittest.main()
