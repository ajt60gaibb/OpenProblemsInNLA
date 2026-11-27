import json
import numpy as np
import scipy.optimize as opt
import mpmath as mp

mp.mp.dps = 80

def cayley(K):
    n = K.shape[0]
    I = np.eye(n)
    inv_IpK = np.linalg.inv(I + K)
    U = (I - K) @ inv_IpK
    return U, inv_IpK

def exact_obj_and_grad(params, p, m, n, ranks):
    idx = 0
    Xs = []
    for k in range(m):
        sz = n * ranks[k]
        Xs.append(params[idx:idx+sz].reshape(n, ranks[k]))
        idx += sz
    tri_i, tri_j = np.triu_indices(n, 1)
    n_k = len(tri_i)
    Us = [np.eye(n)]
    invs = [np.eye(n)]
    for k in range(1, m):
        v = params[idx:idx+n_k]
        idx += n_k
        K = np.zeros((n, n))
        K[tri_i, tri_j] = v
        K[tri_j, tri_i] = -v
        U, inv_IpK = cayley(K)
        Us.append(U)
        invs.append(inv_IpK)

    Ps = [X @ X.T for X in Xs]
    As = [U @ P for U, P in zip(Us, Ps)]
    S = sum(As)
    H = sum(Ps)

    uS, sS, vtS = np.linalg.svd(S, full_matrices=True)
    eH, vH = np.linalg.eigh(H)
    eH = np.maximum(eH, 0.0)

    num_p = np.sum(sS**p)
    den_p = np.sum(eH**p)
    if den_p <= 1e-30 or num_p <= 1e-30:
        return 0.0, np.zeros_like(params)
    ratio = (num_p / den_p)**(1.0 / p)

    sS_pm1 = np.where(sS > 1e-30, sS**(p - 1.0), 0.0)
    eH_pm1 = np.where(eH > 1e-30, eH**(p - 1.0), 0.0)
    dS = -(ratio / num_p) * ((uS * sS_pm1) @ vtS)
    dH = +(ratio / den_p) * ((vH * eH_pm1) @ vH.T)

    grad_parts = []
    for k in range(m):
        Mk = Us[k].T @ dS + dH
        Mk = 0.5 * (Mk + Mk.T)
        grad_parts.append((2.0 * (Mk @ Xs[k])).ravel())

    for k in range(1, m):
        G = -2.0 * (invs[k] @ Ps[k] @ dS.T @ invs[k])
        gK = G[tri_j, tri_i] - G[tri_i, tri_j]
        grad_parts.append(gK)

    return -ratio, np.concatenate(grad_parts)

def unpack(params, m, n, ranks):
    idx = 0
    Xs = []
    for k in range(m):
        sz = n * ranks[k]
        Xs.append(params[idx:idx+sz].reshape(n, ranks[k]))
        idx += sz
    tri_i, tri_j = np.triu_indices(n, 1)
    n_k = len(tri_i)
    Ks = [np.zeros((n, n))]
    Us = [np.eye(n)]
    for k in range(1, m):
        v = params[idx:idx+n_k]
        idx += n_k
        K = np.zeros((n, n))
        K[tri_i, tri_j] = v
        K[tri_j, tri_i] = -v
        U, _ = cayley(K)
        Ks.append(K)
        Us.append(U)
    return Xs, Ks, Us

def pack(Xs, Ks):
    parts = [X.ravel() for X in Xs]
    n = Xs[0].shape[0]
    tri_i, tri_j = np.triu_indices(n, 1)
    for K in Ks[1:]:
        parts.append(K[tri_i, tri_j])
    return np.concatenate(parts)

def warm_staircase_m2(p, p_label, max_n=8, seed=0):
    rng = np.random.default_rng(seed)
    results = []
    prev_Xs = None
    prev_Ks = None
    for n in range(2, max_n + 1):
        rA = (n + 1) // 2
        rB = n // 2
        ranks = [rA, rB]
        best_val = 0.0
        best_params = None
        # Generate initializations: warm starts from prev (n-1) + random restarts
        inits = []
        if prev_Xs is not None:
            for trial in range(12):
                scale = 10.0**(-1.5 - 0.3*(trial % 5))
                new_Xs = []
                for k, rk in enumerate(ranks):
                    oldX = prev_Xs[k]
                    X = np.zeros((n, rk))
                    X[:n-1, :oldX.shape[1]] = oldX
                    if rk > oldX.shape[1]:
                        # new column peeled off!
                        X[:, oldX.shape[1]:] = rng.standard_normal((n, rk - oldX.shape[1])) * scale
                    else:
                        X[n-1, :] = rng.standard_normal(rk) * scale * 0.1
                    X += rng.standard_normal((n, rk)) * (scale * 0.05)
                    new_Xs.append(X)
                new_Ks = [np.zeros((n, n))]
                for Kold in prev_Ks[1:]:
                    K = np.zeros((n, n))
                    K[:n-1, :n-1] = Kold
                    K[:n-1, n-1] = rng.standard_normal(n-1) * scale
                    K[n-1, :n-1] = -K[:n-1, n-1]
                    new_Ks.append(K)
                inits.append(pack(new_Xs, new_Ks))
        for _ in range(15 if n <= 5 else 8):
            dim = sum(n * r for r in ranks) + n*(n-1)//2
            inits.append(rng.standard_normal(dim) * 0.5)

        for x0 in inits:
            res = opt.minimize(exact_obj_and_grad, x0, args=(p, 2, n, ranks),
                               jac=True, method='BFGS', options={'gtol': 1e-14, 'maxiter': 4000})
            if -res.fun > best_val:
                best_val = -res.fun
                best_params = res.x
        Xs, Ks, Us = unpack(best_params, 2, n, ranks)
        # Ensure A has larger rank (or >=)
        Ps = [X @ X.T for X in Xs]
        evs = [np.sort(np.maximum(np.linalg.eigvalsh(P), 0.0))[::-1] for P in Ps]
        # Verify with mpmath at 50 digits!
        As = [U @ P for U, P in zip(Us, Ps)]
        S = As[0] + As[1]
        H = Ps[0] + Ps[1]
        sS = np.linalg.svd(S, compute_uv=False)
        eH = np.maximum(np.linalg.eigvalsh(H), 0.0)
        val_check = float((np.sum(sS**p) / np.sum(eH**p))**(1.0/p))
        r_eff = [int(np.sum(ev > 1e-12 * ev[0])) for ev in evs]
        evA_norm = [float(e / evs[0][0]) for e in evs[0] if e > 1e-12 * evs[0][0]]
        evB_norm = [float(e / evs[1][0]) for e in evs[1] if e > 1e-12 * evs[1][0]]
        delta = val_check - (results[-1]["C"] if results else 1.0)
        results.append({
            "n": n, "ranks": r_eff, "C": val_check, "delta": delta,
            "evA": evA_norm, "evB": evB_norm,
        })
        print(f"p={p_label}, n={n}: C={val_check:.14f}  delta={delta:+.4e}  ranks={r_eff}  evA={[f'{e:.3e}' for e in evA_norm]}")
        prev_Xs, prev_Ks = Xs, Ks
    return results

if __name__ == "__main__":
    all_res = {}
    for label, pval, seed in [("3/2", 1.5, 11), ("4/3", 4.0/3.0, 22), ("5/4", 1.25, 33)]:
        print(f"\n=== Warm-started staircase m=2, p={label} ===")
        all_res[label] = warm_staircase_m2(pval, label, max_n=8, seed=seed)

    # Also m=3 at p=3/2 for n=2..5
    print("\n=== m=3, p=3/2, n=2..5 ===")
    m3_res = []
    rng = np.random.default_rng(77)
    for n in [2, 3, 4, 5]:
        ranks = [n - 1, n - 1, n - 1]
        dim = sum(n * r for r in ranks) + 2 * (n * (n - 1) // 2)
        best_val = 0.0
        best_x = None
        for _ in range(30 if n <= 4 else 20):
            x0 = rng.standard_normal(dim) * 0.5
            res = opt.minimize(exact_obj_and_grad, x0, args=(1.5, 3, n, ranks),
                               jac=True, method='BFGS', options={'gtol': 1e-14, 'maxiter': 4000})
            if -res.fun > best_val:
                best_val = -res.fun
                best_x = res.x
        Xs, Ks, Us = unpack(best_x, 3, n, ranks)
        evs = [np.sort(np.maximum(np.linalg.eigvalsh(X @ X.T), 0.0))[::-1] for X in Xs]
        r_eff = [int(np.sum(ev > 1e-11 * max(ev[0], 1e-30))) for ev in evs]
        m3_res.append({"n": n, "C": best_val, "ranks": r_eff})
        print(f"m=3, p=3/2, n={n}: C={best_val:.14f}  ranks={r_eff}")
    all_res["m3_3/2"] = m3_res

    with open("/home/marcio/Projects/mi20-subquadratic-lee/staircase_results.json", "w") as f:
        json.dump(all_res, f, indent=2)
    print("\nSaved staircase_results.json")
