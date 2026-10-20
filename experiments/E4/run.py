# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E4 (узел I32): нули Delta(mu) из I32 против спектра L_c y = -y''(x) - c y''(-x) на (-1,1).
Условия U1: al1 y(-1)+be1 y'(-1)=0, U2: al2 y(1)+be2 y'(1)=0.
Метод 1: коллокация Чебышёва-Лобатто, N = 60, 90, 120.
Метод 2: конечные разности 2-го порядка, n = 2000, 4000, Ричардсон.
"""
import time
import numpy as np
import scipy.linalg as sl
import scipy.sparse as sp
import scipy.sparse.linalg as sps
from scipy.optimize import brentq

K = 30


def cheb(N):
    x = np.cos(np.pi * np.arange(N + 1) / N)
    c = np.hstack([2, np.ones(N - 1), 2]) * (-1) ** np.arange(N + 1)
    X = np.tile(x, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D -= np.diag(D.sum(axis=1))
    return D, x


def colloc(c, bc, N):
    """Все конечные собственные значения lambda; x[0]=1, x[N]=-1."""
    al1, be1, al2, be2 = bc
    D, x = cheb(N)
    D2 = D @ D
    Rm = np.eye(N + 1)[::-1]            # (R f)_j = f(-x_j) = f_{N-j}
    A = -D2 - c * Rm @ D2               # y''(-x_j) = (D2 y)_{N-j}
    B = np.eye(N + 1)
    A[0, :] = al2 * np.eye(N + 1)[0] + be2 * D[0]     # x=1: U2
    A[N, :] = al1 * np.eye(N + 1)[N] + be1 * D[N]     # x=-1: U1
    B[0, :] = 0
    B[N, :] = 0
    w = sl.eig(A, B, right=False)
    return w[np.isfinite(w)]


def fd_matrix(c, bc, n):
    """Сетка x_j=-1+jh, j=0..n. Граничные неизвестные исключены условиями с
    односторонними разностями 2-го порядка. Возвращает матрицу на внутренних узлах."""
    al1, be1, al2, be2 = bc
    h = 2.0 / n
    m = n - 1
    E = np.zeros((n + 1, m))
    for j in range(1, n):
        E[j, j - 1] = 1
    d1 = al1 - 3 * be1 / (2 * h)
    E[0, 0] = -be1 * 4 / (2 * h) / d1
    E[0, 1] = be1 / (2 * h) / d1
    d2 = al2 + 3 * be2 / (2 * h)
    E[n, m - 1] = be2 * 4 / (2 * h) / d2
    E[n, m - 2] = -be2 / (2 * h) / d2
    D2 = sp.lil_matrix((n + 1, n + 1))
    for j in range(1, n):
        D2[j, j - 1] = 1 / h**2
        D2[j, j] = -2 / h**2
        D2[j, j + 1] = 1 / h**2
    D2 = D2.tocsr()
    Rm = sp.csr_matrix(np.eye(n + 1)[::-1])
    L = -(D2 + c * Rm @ D2)
    return sp.csr_matrix(L[1:n, :] @ sp.csr_matrix(E))


def fd_eigs(c, bc, n, k):
    A = fd_matrix(c, bc, n).tocsc()
    return sps.eigs(A, k=k + 15, sigma=-5.0, which="LM", return_eigenvectors=False)


def Delta(mu, c, bc, swap=False):
    al1, be1, al2, be2 = bc
    lp, lm = (1 + c) ** -0.5, (1 - c) ** -0.5
    if swap:
        lp, lm = lm, lp
    rp, rm = lp, lm
    mu = np.asarray(mu, dtype=complex)
    Cp, Sp, Cm, Sm = np.cos(mu * lp), np.sin(mu * lp), np.cos(mu * lm), np.sin(mu * lm)
    return (-2 * al1 * al2 * Cp * Sm - 2 * be1 * be2 * mu**2 * rp * rm * Sp * Cm
            + mu * (al1 * be2 - al2 * be1) * (rp * Sp * Sm - rm * Cp * Cm))


def delta_roots(c, bc, swap, mumax):
    mus = np.linspace(1e-6, mumax, int(mumax * 400))
    f = Delta(mus, c, bc, swap).real
    r = []
    for i in range(len(mus) - 1):
        if f[i] * f[i + 1] < 0:
            r.append(brentq(lambda t: Delta(t, c, bc, swap).real, mus[i], mus[i + 1], xtol=1e-14, rtol=1e-14))
    return np.array(r)


def delta_neg_roots(c, bc, swap):
    """lambda=-t^2<0: mu=i t; здесь Delta(it)/i вещественна."""
    ts = np.linspace(1e-6, 8, 8000)
    g = lambda t: (Delta(1j * t, c, bc, swap) / 1j).real
    f = g(ts)
    return np.array([-brentq(g, ts[i], ts[i + 1], xtol=1e-14) ** 2
                     for i in range(len(ts) - 1) if f[i] * f[i + 1] < 0])


def split(w, tol=1e-6):
    real = np.abs(w.imag) < tol * np.maximum(1, np.abs(w.real))
    pos = np.sort(w[real & (w.real > 0)].real)
    neg = np.sort(w[real & (w.real <= 0)].real)
    cx = w[~real]
    return pos, neg, cx


def run_case(c, bc, swaps=(False, True)):
    print(f"\n=== c={c}, bc={bc} ===")
    mu = {}
    for N in (60, 90, 120):
        pos, neg, cx = split(colloc(c, bc, N))
        mu[N] = np.sqrt(pos[:K])
        print(f"colloc N={N}: lambda>0 (всего): {len(pos)}, lambda<=0: {np.round(neg[np.abs(neg)<1e3],8)}, "
              f"невещественных с |lam|<1e3: {np.sum(np.abs(cx)<1e3)}")
    print(f"colloc: max|mu(60)-mu(120)|={np.max(np.abs(mu[60]-mu[120])):.2e}, "
          f"max|mu(90)-mu(120)|={np.max(np.abs(mu[90]-mu[120])):.2e}")
    ref = mu[120]
    fds = {}
    for n in (2000, 4000):
        pos, neg, cx = split(fd_eigs(c, bc, n, K))
        fds[n] = np.sqrt(pos[:K])
    rich = (4 * fds[4000] - fds[2000]) / 3
    print(f"FD против colloc (30 первых mu): n=2000: {np.max(np.abs(fds[2000]-ref)):.2e}; "
          f"n=4000: {np.max(np.abs(fds[4000]-ref)):.2e}; Ричардсон: {np.max(np.abs(rich-ref)):.2e}")
    out = {}
    for swap in swaps:
        tag = "обмен" if swap else "как записано"
        r = delta_roots(c, bc, swap, ref[-1] + 3)
        negr = delta_neg_roots(c, bc, swap)
        ordd = np.max(np.abs(r[:K] - ref)) if len(r) >= K else np.inf
        near = np.max([np.min(np.abs(r - m)) for m in ref])
        print(f"Delta ({tag}): корней mu>0 до {ref[-1]+3:.1f}: {len(r)}; lambda<0: {np.round(negr,6)}; "
              f"max|mu_k(Delta)-mu_k(colloc)| по номеру: {ordd:.2e}; по ближайшему: {near:.2e}")
        out[swap] = r
    return ref, out


if __name__ == "__main__":
    t0 = time.time()
    np.set_printoptions(linewidth=140)
    print("Проверка метода")
    pos = split(colloc(0.0, (1, 0, 0, 1), 120))[0]
    ex = np.pi * (np.arange(K) + 0.5) / 2
    print(f"c=0 Дирихле-Нейман, colloc N=120: max|mu-pi(k+1/2)/2| = {np.max(np.abs(np.sqrt(pos[:K])-ex)):.2e}")
    # c=0, y(-1)+y'(-1)=0, y'(1)=0. y=A cos(mu(x+1))+B sin(mu(x+1)): A+mu B=0, -A mu sin2mu + B mu cos2mu=0
    g = lambda m: m * np.cos(2 * m) + m**2 * np.sin(2 * m)
    mm = np.linspace(1e-3, 50, 200000)
    gv = g(mm)
    roots = np.array([brentq(g, mm[i], mm[i + 1], xtol=1e-14) for i in range(len(mm) - 1) if gv[i] * gv[i + 1] < 0][:K])
    pos0, neg0, cx0 = split(colloc(0.0, (1, 1, 0, 1), 120))
    print(f"c=0 Робен-Нейман: lambda<=0 (colloc): {np.round(neg0[np.abs(neg0)<1e3],8)}; "
          f"max|mu - скалярный определитель| = {np.max(np.abs(np.sqrt(pos0[:K])-roots)):.2e}")
    r = delta_roots(0.0, (1, 1, 0, 1), False, 52)
    print(f"c=0: нули Delta(I32) против скалярного определителя: max разность первых 30 = {np.max(np.abs(r[:K]-roots)):.2e}")
    wf = split(fd_eigs(0.0, (1, 1, 0, 1), 2000, K))[0]
    print(f"c=0: FD n=2000 против скалярного определителя: {np.max(np.abs(np.sqrt(wf[:K])-roots)):.2e}")
    wf = split(fd_eigs(0.0, (1, 1, 0, 1), 4000, K))[0]
    print(f"c=0: FD n=4000: {np.max(np.abs(np.sqrt(wf[:K])-roots)):.2e}")

    bc = (1, 1, 0, 1)
    allres = {c: run_case(c, bc) for c in (0.5, -0.5)}
    for c in (0.5, -0.5):
        ref, out = allres[c]
        print(f"\nc={c}: k, mu_k(colloc N=120), mu_k(Delta как записано), mu_k(Delta с обменом)")
        for k in range(K):
            row = f"{k+1:3d} {ref[k]:.10f}"
            for s in (False, True):
                row += f"  {out[s][k]:.10f}" if k < len(out[s]) else "  --"
            print(row)
    # --- Случаи 1 и 2 формулы (A) (дополнение) ---
    # Классификация по beta: случай 1 -- be1*be2 != 0; случай 2 -- be1=be2=0; случай 3 -- ровно одно be_j=0.
    # Набор (1,1,0,1) выше (y(-1)+y'(-1)=0, y'(1)=0) имеет be1=be2=1, то есть это СЛУЧАЙ 1, не 3.
    THR = 1e-8
    cases = {
        "случай 1, набор (1,1,0,1)": (1, 1, 0, 1),
        "случай 1, набор (2,1,-1,3)": (2, 1, -1, 3),
        "случай 1, набор (1,-2,3,1)": (1, -2, 3, 1),
        "случай 2, Дирихле (1,0,1,0)": (1, 0, 1, 0),
    }
    summary = []
    for name, bc in cases.items():
        for c in (0.5, -0.5):
            print(f"\n##### {name}, c={c}")
            ref, out = run_case(c, bc, swaps=(False,))
            d = np.max(np.abs(out[False][:K] - ref)) if len(out[False]) >= K else np.inf
            summary.append((name, c, d, len(out[False])))
    print("\nСводка (порог опровержения 1e-8, максимум по первым 30 mu):")
    for name, c, d, nr in summary:
        print(f"{name:32s} c={c:+.1f}  max|dmu|={d:.2e}  {'согласуется' if d < THR else 'ОПРОВЕРГАЕТ'}")
    print(f"\nвремя: {time.time()-t0:.1f} c")
