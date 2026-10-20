# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E3 (узел I28): максимум числа значений omega=sqrt(lambda) в окне |Re omega - x| < h.

L_a y = -y''(x) - a(x) y''(-x) на (-1,1), Дирихле. a = 1/2 (контроль, C3), 1/2+x/4, 1/2+2x/5.
Метод 1: Галёркин в базисе s_n = sin(n pi (x+1)/2) (ортонормирован), R s_n = (-1)^(n+1) s_n,
  B = K^{1/2} (I + (alpha I + gamma X) R) K^{1/2},  X_mn = int x s_m s_n, K = diag((n pi/2)^2),
  N = 800, 1200, 1600. Метод 2: коллокация Чебышёва-Лобатто, N = 700.
h = 1 + 3 W, W = winW(beta) = 12 beta + 12 (MMWindowCut.lean), beta = b1 = nu (1+sqrt k) 2c,
  nu = (1-sqrt k)^(-1/2), k = sup a(x)a(-x), c = sup |a'|/(2a) (r = sqrt a, C10).
"""
import time
import numpy as np
import scipy.linalg as la
from numpy.polynomial.legendre import leggauss

T0 = time.time()
NVAL = 400
CASES = {  # name: (alpha, gamma)
    "a=1/2": (0.5, 0.0),
    "a=1/2+x/4": (0.5, 0.25),
    "a=1/2+2x/5": (0.5, 0.4),
}
NLIST = (800, 1200, 1600)


def beta_of(alpha, gamma):
    xs = np.linspace(-1, 1, 200001)
    a = alpha + gamma * xs
    kap = np.max(a * a[::-1])
    nu = 1 / np.sqrt(1 - np.sqrt(kap))
    c = np.max(np.abs(gamma) / (2 * a)) if gamma else 0.0
    return nu * (1 + np.sqrt(kap)) * 2 * c, kap, c


def exact_half():
    n = np.arange(1, 400)
    lam = np.concatenate([1.5 * np.pi**2 * (n - 0.5) ** 2, 0.5 * np.pi**2 * n**2])
    return np.sort(lam)[:NVAL]


def xmatrix(N, Q):
    x, w = leggauss(Q)
    S = np.sin(np.outer(x + 1, np.arange(1, N + 1)) * np.pi / 2)
    return S, x, w, (S * (w * x)[:, None]).T @ S


def galerkin(alpha, gamma, N, X, vectors=False):
    n = np.arange(1, N + 1)
    k = n * np.pi / 2
    R = (-1.0) ** (n + 1)
    M = alpha * np.eye(N) + gamma * X
    B = k[:, None] * (np.eye(N) + M * R[None, :]) * k[None, :]
    if vectors:
        return la.eig(B)
    return la.eigvals(B), None


def first(lam, m=NVAL + 30):
    # a вещественна: спектр симметричен относительно вещественной оси; пара берётся с Im >= 0,
    # чтобы порядок внутри пары не зависел от округления
    lam = lam.real + 1j * np.abs(lam.imag)
    o = np.argsort(np.abs(lam))
    return lam[o][:m]


def omegas(lam):
    return np.sqrt(lam.astype(complex))


def window_max(om, n, h):
    """max_x #{k<=n : |Re om_k - x| < h}; all: все окна, full: окна с x+h <= Re om_n."""
    r = np.sort(om[:n].real)
    cnt_all = 0
    cnt_full = None
    j = 0
    for i in range(n):
        while j < n and r[j] < r[i] + 2 * h:
            j += 1
        c = j - i
        cnt_all = max(cnt_all, c)
        if r[i] + 2 * h <= r[-1]:
            cnt_full = c if cnt_full is None else max(cnt_full, c)
    return cnt_all, cnt_full


def cheb_eigs(alpha, gamma, N):
    k = np.arange(N + 1)
    t = np.cos(np.pi * k / N)
    c = np.ones(N + 1)
    c[0] = 2
    c[-1] = 2
    c = c * (-1.0) ** k
    Xg = np.tile(t, (N + 1, 1)).T
    dX = Xg - Xg.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D = D - np.diag(D.sum(axis=1))
    D2 = (D @ D)[1:-1, 1:-1]
    ti = t[1:-1]
    R = np.eye(N - 1)[::-1]
    A = (np.eye(N - 1) + np.diag(alpha + gamma * ti) @ R) @ (-D2)
    return la.eigvals(A)


def fmt(v):
    return "-" if v is None else str(v)


print("E3: окна для omega = sqrt(lambda); h = 1 + 3 W, W = 12 beta + 12")
print("Параметры:", dict(NVAL=NVAL, NLIST=NLIST))
params = {}
for name, (al, ga) in CASES.items():
    b, kap, c = beta_of(al, ga)
    W = 12 * b + 12
    params[name] = 1 + 3 * W
    print(f"{name}: kappa={kap:.6f} c={c:.6f} beta=b1={b:.6f} W={W:.4f} h=1+3W={1+3*W:.4f}")

# ------------------------------------------------ проверка метода
print("\n== Проверка метода")
_, _, _, X0 = xmatrix(800, 3 * 800 + 400)
_, _, _, X1 = xmatrix(800, 3 * 800 + 1400)
print(f"X: разность Q=2800 против Q=3800 (N=800): {np.max(np.abs(X0-X1)):.2e}")
ex = exact_half()
for N in NLIST:
    lam, _ = galerkin(0.5, 0.0, N, np.zeros((N, N)))
    f = first(lam, NVAL)
    lg = np.sort(f.real)
    print(f"a=1/2 Галёркин N={N}: max отн. ошибка первых {NVAL} lambda против C3 = "
          f"{np.max(np.abs(lg-ex)/ex):.2e}; max |Im lambda| = {np.max(np.abs(f.imag)):.1e}")
lamc = np.sort(first(cheb_eigs(0.5, 0.0, 700), NVAL).real)
print(f"a=1/2 коллокация N=700: max отн. ошибка первых 300 против C3 = "
      f"{np.max(np.abs(lamc[:300]-ex[:300])/ex[:300]):.2e}")

# ------------------------------------------------ основной расчёт
spectra = {}
Xs = {}
for N in NLIST:
    Xs[N] = xmatrix(N, 3 * N + 400)
for name, (al, ga) in CASES.items():
    spectra[name] = {}
    for N in NLIST:
        t = time.time()
        lam, _ = galerkin(al, ga, N, Xs[N][3])
        spectra[name][N] = first(lam)
        print(f"{name} N={N}: eig за {time.time()-t:.1f} с")

print("\n== Сходимость по N (первые 400 lambda, сортировка по |lambda|)")
for name in CASES:
    f = {N: spectra[name][N][:NVAL] for N in NLIST}
    ref = f[NLIST[-1]]
    for N in NLIST[:-1]:
        d = np.abs(f[N] - ref) / np.abs(ref)
        print(f"{name}: N={N} против N={NLIST[-1]}: max отн. разность lambda = {d.max():.2e}; "
              f"номера с разностью > 1e-6: {list(np.where(d>1e-6)[0][:5]+1)}")
    nonreal = int(np.sum(np.abs(ref.imag) > 1e-8 * np.abs(ref)))
    gap = np.abs(spectra[name][NLIST[-1]][NVAL]) / np.abs(ref[-1])
    print(f"{name}: нереальных среди 400: {nonreal}; max|Im omega|={np.max(np.abs(omegas(ref).imag)):.2e}; "
          f"|lam_401|/|lam_400| = {gap:.5f}")

print("\n== Коллокация Чебышёва N=700, первые 200 lambda против Галёркина N=1600")
for name, (al, ga) in CASES.items():
    lc = first(cheb_eigs(al, ga, 700), 200)
    lg = spectra[name][NLIST[-1]][:200]
    o1 = np.argsort(np.abs(lc))
    o2 = np.argsort(np.abs(lg))
    d = np.abs(lc[o1] - lg[o2]) / np.abs(lg[o2])
    print(f"{name}: max отн. разность по первым 100 = {d[:100].max():.2e}, по первым 200 = {d.max():.2e}")

print("\n== Невязки в L2 для L_a и обусловленность базиса (N=1600, первые 400 пар)")
N = NLIST[-1]
S, xq, wq, Xn = Xs[N]
n = np.arange(1, N + 1)
k = n * np.pi / 2
Rm = (-1.0) ** (n + 1)
for name, (al, ga) in CASES.items():
    lam, V = galerkin(al, ga, N, Xn, vectors=True)
    o = np.argsort(np.abs(lam))[:NVAL]
    Vi = la.inv(V)
    kap_k = np.linalg.norm(V[:, o], axis=0) * np.linalg.norm(Vi[o, :], axis=1)
    C = V[:, o] / k[:, None]
    ygrid = S @ C
    ypp = S @ (C * (k**2)[:, None])
    yrefl = S @ ((C * Rm[:, None]) * (k**2)[:, None])
    a = al + ga * xq
    res = (ypp + a[:, None] * yrefl) - lam[o][None, :] * ygrid
    rn = np.sqrt((wq[:, None] * np.abs(res) ** 2).sum(0))
    yn = np.sqrt((wq[:, None] * np.abs(ygrid) ** 2).sum(0))
    rel = rn / (np.abs(lam[o]) * yn)
    print(f"{name}: невязка ||L y - lam y||/(|lam| ||y||): max={rel.max():.2e}, медиана={np.median(rel):.2e}; "
          f"kappa_k=||v|| ||w||/|<w,v>| (евкл. по коэфф. B): max={kap_k.max():.3f}")

print("\n== Максимум числа omega в окне |Re omega - x| < h")
print("ячейка M_all/M_full: M_all - все окна среди первых n значений; M_full - окна, целиком левее Re omega_n; '-' - полных окон нет")
ns = (25, 50, 100, 150, 200, 250, 300, 350, 400)
for name in CASES:
    hs = [("h=1+3W", params[name]), ("h=5", 5.0), ("h=20", 20.0), ("h=40", 40.0)]
    cand = {}
    if name == "a=1/2":
        cand["C3 точный"] = omegas(exact_half())
    for N in NLIST:
        cand[f"Галёркин N={N}"] = omegas(np.sort(spectra[name][N][:NVAL].real))
    for hname, h in hs:
        print(f"\n{name}, {hname} = {h:.3f} (длина окна {2*h:.1f})")
        print("  источник".ljust(26) + "".join(f"n={kk}".rjust(12) for kk in ns))
        for src, om in cand.items():
            row = []
            for kk in ns:
                ca, cf = window_max(om, kk, h)
                row.append(f"{ca}/{fmt(cf)}")
            print(f"  {src}".ljust(26) + "".join(r.rjust(12) for r in row))

print("\n== Число значений в окне, полные окна с левым краем в точке спектра (N=1600, n=400)")
for name in CASES:
    om = omegas(np.sort(spectra[name][NLIST[-1]][:NVAL].real))
    r = np.sort(om.real)
    for hname, h in (("h=5", 5.0), ("h=20", 20.0), ("h=40", 40.0), ("h=1+3W", params[name])):
        if 2 * h > r[-1]:
            print(f"{name} {hname}: окно {2*h:.1f} длиннее спектра {r[-1]:.1f}, пропущено")
            continue
        starts = r[r + 2 * h <= r[-1]]
        cnts = np.array([np.sum((r >= s) & (r < s + 2 * h)) for s in starts])
        print(f"{name} {hname}: max={cnts.max()}, min={cnts.min()}, mean={cnts.mean():.2f} по {len(starts)} окнам")
print("\n== Расширение сверх задания: первые 900 значений, h = 1+3W (для a=1/2+2x/5 при 400 значениях полных окон нет)")
NEXT = 900
NE = (1600, 2000)
nsx = (300, 400, 500, 600, 700, 800, 900)
for name, (al, ga) in CASES.items():
    sp = {}
    for N in NE:
        if N not in Xs:
            Xs[N] = xmatrix(N, 3 * N + 400)
        lam, _ = galerkin(al, ga, N, Xs[N][3])
        sp[N] = first(lam, NEXT)
    d = np.abs(sp[NE[0]] - sp[NE[1]]) / np.abs(sp[NE[1]])
    print(f"{name}: N={NE[0]} против N={NE[1]}, 900 значений: max отн. разность lambda = {d.max():.2e}; "
          f"нереальных: {int(np.sum(np.abs(sp[NE[1]].imag) > 1e-8*np.abs(sp[NE[1]])))}; "
          f"Re omega_900 = {omegas(np.sort(sp[NE[1]].real))[-1].real:.1f}")
    h = params[name]
    print("  источник".ljust(30) + "".join(f"n={kk}".rjust(12) for kk in nsx))
    for N in NE:
        om = omegas(np.sort(sp[N].real))
        row = []
        for kk in nsx:
            ca, cf = window_max(om, kk, h)
            row.append(f"{ca}/{fmt(cf)}")
        print(f"  {name} h={h:.1f} N={N}".ljust(30) + "".join(r.rjust(12) for r in row))
    r = np.sort(omegas(np.sort(sp[NE[1]].real)).real)
    if 2 * h <= r[-1]:
        starts = r[r + 2 * h <= r[-1]]
        cnts = np.array([np.sum((r >= s) & (r < s + 2 * h)) for s in starts])
        print(f"  полные окна n=900: max={cnts.max()}, min={cnts.min()}, mean={cnts.mean():.2f}, число окон {len(starts)}")
print(f"\nвремя: {time.time()-T0:.0f} с")
