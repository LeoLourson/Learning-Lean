# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E5 (узел I33, пункт iii): Грам собственных функций L_a y = -y''(x) - a(x) y''(-x),
y(-1)=0, y'(1)=0, a = 0 (контроль), 0.9, 1/2 + x/4.
Метод 1 (основной): Галёркин по Лежандру для w=-y'' в форме (I+aR)w = lam*G w, G w = y
  (G: -y''=w, y(-1)=0, y'(1)=0), a=alpha+gamma x, n = 1600, 2000, 2400; y находится точно.
Метод 2: коллокация Чебышёва (n=400, 600), первые 40 значений.
Метод 3 (a=0.9): корни Delta = t cos s cos t - s sin s sin t и явные функции.
(Первая попытка: Галёркин в базисе sin(nu_k(x+1)) сходится медленно, см. run_sine_galerkin_first_attempt.log.)
"""
import time
import numpy as np
from numpy.polynomial.legendre import leggauss, legvander
from scipy.linalg import eig, svdvals
from scipy.optimize import brentq

NLIST = [10, 20, 50, 100, 150, 200, 300, 400]
NS = [1600, 2000, 2400]


def integ(C):
    """Коэффициенты Лежандра (P_k) первообразной int_{-1}^x; вход K x N, выход (K+1) x N."""
    K, N = C.shape
    out = np.zeros((K + 1, N), dtype=C.dtype)
    k = np.arange(K)
    Ck = C / (2 * k + 1)[:, None]
    out[1:K + 1] += Ck           # +C_k/(2k+1) в P_{k+1}
    out[0:K - 1] -= Ck[1:]       # -C_k/(2k+1) в P_{k-1}, k>=1
    out[0] += C[0]               # int_{-1}^x P_0 = P_0 + P_1: P_1 уже даёт Ck[0]=C[0]
    return out


def legendre_solve(alpha, gamma, n, Nmax):
    k = np.arange(n)
    sc = np.sqrt((2 * k + 1) / 2)          # p_k = sc * P_k, ортонормированный базис
    off = (k[:-1] + 1) / np.sqrt((2 * k[:-1] + 1) * (2 * k[:-1] + 3))
    X = np.diag(off, 1) + np.diag(off, -1)
    Rv = (-1.0) ** k
    S = np.eye(n) + (alpha * np.eye(n) + gamma * X) * Rv[None, :]   # проекция I + aR
    C = np.eye(n) * sc[:, None]            # Лежандр-коэффициенты p_k = sc_k P_k
    F = integ(C)
    F1 = 2 * C[0]                           # int_{-1}^1 p_k
    Yc = np.zeros((n + 2, n))
    Yc[0] += F1
    Yc[1] += F1
    Yc -= integ(F)                          # y = F1*(x+1) - int F, G p_k
    Y = Yc * np.sqrt(2 / (2 * np.arange(n + 2) + 1))[:, None]       # ортонорм. коэфф.
    Gm = Y[:n]
    T = np.linalg.solve(S, Gm)
    mu, V = eig(T)
    idx = np.argsort(-mu.real)[:Nmax]
    mu, V = mu[idx], V[:, idx]
    V = V / np.linalg.norm(V, axis=0)
    return 1 / mu, V, Y @ V


def residuals(lam, W, Yv, alpha, gamma, N):
    n = W.shape[0]
    x, w = leggauss(n + 8)
    Vw = legvander(x, n + 1) * np.sqrt((2 * np.arange(n + 2) + 1) / 2)
    wv = Vw[:, :n] @ W[:, :N]
    yv = Vw @ Yv[:, :N]
    a = (alpha + gamma * x)[:, None]
    r = wv + a * wv[::-1] - lam[:N] * yv
    return np.sqrt(w @ np.abs(r) ** 2) / np.sqrt(w @ np.abs(lam[:N] * yv) ** 2)


def cond_gram(C):
    s = svdvals(C)
    return (s[0] / s[-1]) ** 2


def gaps(lam, N):
    mu = np.sqrt(lam[:N].astype(complex))
    d = np.abs(mu[:, None] - mu[None, :]) + np.eye(N) * 1e9
    i, j = np.unravel_index(np.argmin(d), d.shape)
    return d.min(), (min(i, j) + 1, max(i, j) + 1), mu


def cheb(afun, n=400):
    j = np.arange(n + 1)
    x = np.cos(np.pi * j / n)
    c = np.hstack([2, np.ones(n - 1), 2]) * (-1.0) ** j
    X = np.tile(x, (n + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(n + 1))
    D = D - np.diag(D.sum(axis=1))
    D2 = D @ D
    A = -D2 - np.diag(afun(x)) @ D2[::-1, :]
    Bm = np.eye(n + 1)
    A[0, :] = D[0, :]; Bm[0, :] = 0          # y'(1)=0
    A[n, :] = 0; A[n, n] = 1; Bm[n, :] = 0   # y(-1)=0
    lam = eig(A, Bm, right=False)
    lam = lam[np.isfinite(lam)]
    return lam[np.argsort(lam.real)]


def nrm(Y):
    return Y / np.linalg.norm(Y, axis=0)


def run_case(label, alpha, gamma):
    afun = lambda x: alpha + gamma * x
    print(f"\n=== {label} ===", flush=True)
    res = {}
    for n in NS:
        t0 = time.time()
        res[n] = legendre_solve(alpha, gamma, n, 450)
        lam = res[n][0]
        print(f"n={n}: {time.time()-t0:.1f} s; max|Im lam|/|lam| (первые 400) = "
              f"{np.max(np.abs(lam[:400].imag)/np.abs(lam[:400])):.2e}", flush=True)
    print("\nN | cond n=1600 | cond n=2000 | cond n=2400 | отн.разн. cond(2400,2000) | "
          "max|dlam|/lam (2400,2000) | max|d sqrt lam| (2400,2000)")
    for N in NLIST:
        cs = [cond_gram(nrm(res[n][2][:, :N])) for n in NS]
        l2, l1 = res[2400][0][:N], res[2000][0][:N]
        dl = np.max(np.abs(l2 - l1) / np.abs(l2))
        dm = np.max(np.abs(np.sqrt(l2.astype(complex)) - np.sqrt(l1.astype(complex))))
        print(f"{N} | " + " | ".join(f"{c:.8g}" for c in cs) +
              f" | {abs(cs[2]-cs[1])/cs[2]:.1e} | {dl:.1e} | {dm:.1e}")
    lam, W, Yv = res[2400]
    r = residuals(lam, W, Yv, alpha, gamma, 400)
    print("Невязка (L2, отн. к ||lam y||), max по первым N:",
          "; ".join(f"N={N}: {r[:N].max():.1e}" for N in [10, 50, 100, 200, 300, 400]))
    Y = nrm(Yv[:, :400])
    print("sigma_min/sigma_max Грамма (n=2400): " + "; ".join(
        f"N={N}: {svdvals(Y[:, :N])[-1]:.4f}/{svdvals(Y[:, :N])[0]:.4f}" for N in NLIST))
    print("\nЗазоры sqrt(lam) (n=2400):")
    for N in [50, 100, 200, 400]:
        g, (i, j), mu = gaps(lam, N)
        print(f"  N={N}: min|mu_j-mu_k| = {g:.5f} при (j,k)=({i},{j}); "
              f"среднее расстояние (mu_N-mu_1)/(N-1) = {(mu[N-1].real-mu[0].real)/(N-1):.5f}")
    mu = np.sqrt(lam[:400].astype(complex))
    dmu = np.diff(mu.real)
    for lo, hi in [(0, 100), (100, 200), (200, 300), (300, 399)]:
        print(f"  соседние зазоры k in [{lo+1},{hi}]: min {dmu[lo:hi].min():.5f}, max {dmu[lo:hi].max():.5f}")
    print(f"  max|Im sqrt lam|, первые 400: {np.abs(mu.imag).max():.2e}")
    lc = cheb(afun, 400)
    lc2 = cheb(afun, 600)
    print(f"\nЧебышёв: первые 40, max отн. разность n=400 / n=600 = "
          f"{np.max(np.abs(lc2[:40]-lc[:40])/np.abs(lc[:40])):.2e}; Лежандр(2400) / Чебышёв(600) = "
          f"{np.max(np.abs(lam[:40]-lc2[:40])/np.abs(lam[:40])):.2e}")
    return lam, W


def exact_roots(a, nroots=400):
    sp, sm = np.sqrt(1 + a), np.sqrt(1 - a)
    D = lambda m: (m / sm) * np.cos(m / sp) * np.cos(m / sm) - (m / sp) * np.sin(m / sp) * np.sin(m / sm)
    grid = np.arange(1e-6, 360, 0.004)
    f = D(grid)
    roots = [brentq(D, grid[i], grid[i + 1], xtol=1e-14) for i in np.nonzero(f[:-1] * f[1:] < 0)[0]]
    return np.array(roots[:nroots])


def exact_gram(a, mus, Q=8000):
    x, w = leggauss(Q)
    sp, sm = np.sqrt(1 + a), np.sqrt(1 - a)
    Y = np.empty((len(mus), Q))
    for k, m in enumerate(mus):
        s, t = m / sp, m / sm
        y = np.sin(t) * np.cos(s * x) + np.cos(s) * np.sin(t * x)
        Y[k] = y * np.sqrt(w) / np.sqrt(np.sum(w * y * y))
    return Y.T


if __name__ == "__main__":
    T0 = time.time()
    print("=== Проверка метода: a=0 ===")
    lam0, W0, Y0 = legendre_solve(0.0, 0.0, 1600, 450)
    ex = ((np.arange(400) + 0.5) * np.pi / 2) ** 2
    print(f"Лежандр: max|lam_k - nu_k^2|/nu_k^2 (k<=400) = {np.max(np.abs(lam0[:400]-ex)/ex):.2e}; "
          f"cond Gram N=400: {cond_gram(nrm(Y0[:, :400])):.12f}")
    lc = cheb(lambda x: 0 * x)
    print(f"Чебышёв a=0: max отн. ошибка первых 40: {np.max(np.abs(lc[:40]-ex[:40])/ex[:40]):.2e}")
    mus = exact_roots(0.9)
    print(f"\nТочный определитель a=0.9: {len(mus)} корней; min зазор = {np.diff(mus[:400]).min():.5f}")
    Yx = exact_gram(0.9, mus[:400])
    print("  cond Gram (явные функции): " + "; ".join(f"N={N}: {cond_gram(Yx[:, :N]):.8g}" for N in NLIST))

    lam9, W9 = run_case("a = 0.9", 0.9, 0.0)
    print(f"\nЛежандр n=2400 против точного определителя (a=0.9): max|sqrt(lam)-mu_exact|, первые 400 = "
          f"{np.max(np.abs(np.sqrt(lam9[:400].real)-mus[:400])):.2e}")
    run_case("a = 1/2 + x/4", 0.5, 0.25)
    print(f"\nВсего {time.time()-T0:.0f} с")
