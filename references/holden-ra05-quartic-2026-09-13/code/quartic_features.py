"""Finite algebra supporting the unrestricted quartic coreset manuscript.

This module implements feature preparation and exact quartic cost decomposition.
It does NOT implement the asymptotic Rothvoss partial-coloring oracle.
All arrays use full tensor coordinates with the inherited Euclidean inner product.
"""
from __future__ import annotations
from dataclasses import dataclass
import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]


def symmetric_power_rows(a: Array, degree: int) -> Array:
    """Full (not compressed) tensor coordinates; suitable for small checks."""
    a = np.asarray(a, dtype=float)
    if a.ndim != 2 or degree < 1:
        raise ValueError("a must be a matrix and degree must be positive")
    out = a.copy()
    for _ in range(degree - 1):
        out = np.einsum("ni,nj->nij", out, a).reshape(len(a), -1)
    return out


def psd_range(a: Array, rtol: float = 1e-11) -> tuple[Array, Array]:
    """Positive eigenvalues and their eigenvectors; zero ranges are permitted."""
    a = (np.asarray(a, dtype=float) + np.asarray(a, dtype=float).T) / 2
    vals, vecs = np.linalg.eigh(a)
    scale = max(float(np.max(np.abs(vals), initial=0)), 1e-300)
    if np.min(vals, initial=0) < -100 * rtol * scale:
        raise ValueError("matrix is not positive semidefinite within tolerance")
    good = vals > rtol * scale
    return vals[good], vecs[:, good]


def invsqrt_positive(a: Array) -> Array:
    vals, vecs = np.linalg.eigh((a + a.T) / 2)
    if np.min(vals) <= 0:
        raise ValueError("positive-definite matrix required")
    return (vecs / np.sqrt(vals)) @ vecs.T


@dataclass
class Features:
    b: Array
    c: Array
    u: Array
    lam: Array
    rho2: Array
    e: Array
    g: Array
    d: Array
    pi: Array
    tau: Array
    t: Array
    mvals: Array
    mvecs: Array
    nvals: Array
    nvecs: Array
    tail_regularizer: Array
    tail_invroot: Array

    @property
    def k(self) -> int:
        return self.b.shape[1]

    @property
    def D(self) -> int:
        return self.e.shape[1]

    @property
    def h(self) -> int:
        return len(self.nvals)

    def atom_matrices(self, indices: NDArray[np.int64] | None = None) -> dict[str, Array]:
        """Matrices before multiplication by a copy's common mass eta."""
        ix = np.arange(len(self.b)) if indices is None else indices
        e, g, d, pi, r2 = self.e[ix], self.g[ix], self.d[ix], self.pi[ix], self.rho2[ix]
        dt = d @ self.tail_invroot
        outer = lambda a, b: np.einsum("ni,nj->nij", a, b) / pi[:, None, None]
        return {
            "X1": outer(e, g), "X2": outer(e, d), "X4": outer(g, d),
            "E": outer(e, e), "G": outer(g, g), "T": outer(dt, dt),
            "v40": r2[:, None] * g / pi[:, None],
            "tail_linear": r2[:, None] * d / pi[:, None],
            "head": self.lam[ix, None] * symmetric_power_rows(self.u[ix], 4) / pi[:, None],
        }


def prepare(b: Array, c: Array, u: Array, lam: Array) -> Features:
    """Prepare proof features from a head/tail split and supplied Lewis data.

    Requires sum ||c_i||^4 = 1 and sum lam_i u_i u_i^T = I.
    A supplied invertible map taking b_i to lam_i**(1/4) u_i is a separate
    mathematical hypothesis; examples in verify.py construct it explicitly.
    """
    b, c, u, lam = map(lambda x: np.asarray(x, dtype=float), (b, c, u, lam))
    if b.ndim != 2 or c.ndim != 2 or u.shape != b.shape or len(c) != len(b):
        raise ValueError("incompatible row arrays")
    n, k = b.shape
    if lam.shape != (n,) or np.any(lam < 0):
        raise ValueError("nonnegative Lewis masses required")
    if not np.allclose((u.T * lam) @ u, np.eye(k), atol=2e-9):
        raise ValueError("Lewis isotropy is not satisfied")
    rho2 = np.sum(c*c, axis=1)
    if not np.isclose(np.sum(rho2*rho2), 1.0, atol=2e-9):
        raise ValueError("tail fourth moment must be one")
    bb = symmetric_power_rows(b, 2)
    mv, mU = psd_range(bb.T @ bb)
    e = (bb @ mU) / np.sqrt(mv)
    nv, nU = psd_range((b.T * rho2) @ b)
    nb = (b @ nU) / np.sqrt(nv) if len(nv) else np.zeros((n, 0))
    g = np.einsum("ni,nj->nij", nb, c).reshape(n, len(nv)*c.shape[1])
    d = symmetric_power_rows(c, 2)
    tau, t = np.sum(e*e, axis=1), np.sum(g*g, axis=1)
    components = [lam/k, tau/e.shape[1], rho2*rho2]
    if len(nv):
        components.append(t/len(nv))
    pi = sum(components) / len(components)
    if np.any(pi <= 0):
        raise ValueError("remove zero input rows before preparation")
    R = d.T @ d + np.eye(d.shape[1])/k
    return Features(b,c,u,lam,rho2,e,g,d,pi,tau,t,mv,mU,nv,nU,R,invsqrt_positive(R))


def projector_query(f: Features, p: Array, theta: Array) -> dict[str, object]:
    """Return all eight quartic error components and their direct sum.

    p may be an orthogonal projector or a positive contraction of rank <= k.
    theta is a signed change in original-row weights.
    """
    p, theta = np.asarray(p, float), np.asarray(theta, float)
    n, k = len(f.b), f.k
    ambient = k + f.c.shape[1]
    if p.shape != (ambient, ambient) or theta.shape != (n,):
        raise ValueError("query or coefficient shape mismatch")
    vals, vecs = np.linalg.eigh((p+p.T)/2)
    if np.min(vals) < -1e-8 or np.max(vals) > 1+1e-8:
        raise ValueError("p must be a positive contraction")
    Q = (vecs * np.sqrt(np.clip(1-vals, 0, 1))) @ vecs.T
    V, W = Q[:, :k], Q[:, k:]
    vb, wc = f.b @ V.T, f.c @ W.T
    A = (V.T @ V).reshape(-1)
    avec = np.sqrt(f.mvals) * (f.mvecs.T @ A)
    if f.h:
        z = (np.sqrt(f.nvals)[:,None] * (f.nvecs.T @ V.T @ W)).reshape(-1)
    else:
        z = np.zeros(0)
    pvec = p[k:, k:].reshape(-1)
    X1 = (f.e.T * theta) @ f.g
    X2 = (f.e.T * theta) @ f.d
    X4 = (f.g.T * theta) @ f.d
    Z3 = (f.g.T * theta) @ f.g
    Z5 = (f.d.T * theta) @ f.d
    bnorm2, cnorm2 = np.sum(vb*vb,1), np.sum(wc*wc,1)
    cross = np.sum(vb*wc,1)
    parts = {
        "head": float(theta @ (bnorm2**2)),
        "cubic_linear": float(4*avec @ X1 @ z),
        "head_tail_constant": float(2*avec @ (f.e.T @ (theta*f.rho2))),
        "head_tail_projected": float(-2*avec @ X2 @ pvec),
        "cross_square": float(4*z @ Z3 @ z),
        "linear_cubic_constant": float(4*z @ (f.g.T @ (theta*f.rho2))),
        "linear_cubic_projected": float(-4*z @ X4 @ pvec),
        "tail_constant": float(theta @ (f.rho2**2)),
        "tail_linear": float(-2*pvec @ (f.d.T @ (theta*f.rho2))),
        "tail_quadratic": float(pvec @ Z5 @ pvec),
    }
    costs = (np.sum((vb+wc)**2,1))**2
    H = float(np.sum(bnorm2**2))
    return {"parts":parts, "sum":sum(parts.values()), "direct":float(theta@costs),
            "cost":float(costs.sum()), "head_cost":H, "a":avec, "z":z,
            "p":pvec, "cross":cross, "head_row_cost":bnorm2**2,
            "tail_row_cost":cnorm2**2, "costs":costs,
            "mixed_quadratic_bound":float(f.rho2@bnorm2)}


def variance_pair(X: Array) -> tuple[Array, Array]:
    X = np.asarray(X, float)
    if X.ndim != 3:
        raise ValueError("expected a sequence of rectangular matrices")
    return np.einsum("nij,nkj->ik", X, X), np.einsum("nji,njk->ik", X, X)


def projected_series_atoms(X: Array, basis: Array) -> Array:
    """Independent-Gaussian atoms for a standard Gaussian on span(basis)."""
    if X.shape[0] != basis.shape[0]:
        raise ValueError("coefficient dimension mismatch")
    return np.einsum("nj,nab->jab", basis, X)


def exact_optimal_block(k: int, N: int, R: int = 2) -> tuple[Array, Array, Array, Array]:
    """Head is provably optimal when N>k and R^2(N-k)>=1.

    Return a tail-normalized version of rows R e_j +/- e_{jt}, with Lewis data.
    """
    if k < 1 or N <= k or R*R*(N-k) < 1:
        raise ValueError("parameters do not meet the stated optimality certificate")
    n = 2*k*N
    scale = n**(-0.25)
    b, c, u = np.zeros((n,k)), np.zeros((n,k*N)), np.zeros((n,k))
    lam = np.full(n, 1/(2*N))
    ell = 0
    for j in range(k):
        for t in range(N):
            for sign in (1,-1):
                b[ell,j] = R*scale
                u[ell,j] = 1
                c[ell,j*N+t] = sign*scale
                ell += 1
    return b,c,u,lam
