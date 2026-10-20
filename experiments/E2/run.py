# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E2 (узел I26): a = x + 1/2 на (-1,1), L_a y = -y''(x) - a(x) y''(-x), Дирихле.

Часть A. ВКБ-квазимода шага 4 идеи I26 около +-x0, x0 = 3/4, на луче arg w = arg(1+ib(x0)).
  Сложение U = (y(x), y(-x)): -U'' = lambda M^{-1} U, M = [[1,a(x)],[a(-x),1]], при p<0
  собственные значения M равны 1 +- ib, b = sqrt(-p); E = [[a,a],[ib,-ib]], U = E V,
  -V'' - 2 B V' - C V = lambda diag(rho+, rho-) V, B = E^{-1}E', C = E^{-1}E'', rho+- = 1/(1 +- ib).
  V = (Z, v):  Z = A exp(i tau sqrt(w) S),  S = int_{x0}^x rho+^{1/2},  A = (1+ib)^{1/4} exp(-int B11)
  (уравнение переноса), v = 2 B21 Z' / (lambda (rho+ - rho-))   (поправка во второй ветви);
  затем умножение на гладкую срезку chi около x0.
  y(x) = u1(x) около x0, y(x) = u2(-x) около -x0. Невязка считается для настоящего L_a на
  равномерной сетке h = 1e-4 конечными разностями 6-го порядка, без использования формул V.
  Варианты: с поправкой v и без неё (v = 0).
Часть B. Собственные пары: Чебышёв-коллокация (N=120,180) и синусный Галёркин (N=120,180);
  kappa_k = ||y_k|| ||z_k|| / |(y_k, z_k)|; контроль a = 1/2 (C3).
"""
import time
import numpy as np
import scipy.linalg as sla
from scipy.integrate import cumulative_trapezoid

T0 = time.time()
np.set_printoptions(linewidth=200)

# ---------------------------------------------------------------- часть A
import sys
sys.stdout.reconfigure(encoding="utf-8")
H = 1e-4
XG = np.linspace(-1, 1, 20001)
X0 = 0.75
I0 = int(round((X0 + 1) / H))
assert abs(XG[I0] - X0) < 1e-12 and I0 == 17500
WIN = 0.2   # полуширина окна около x0 (x0-WIN = 0.55 > 1/2, x0+WIN = 0.95 < 1)


def a_f(x):
    return x + 0.5


def fd2(y, h):
    """6-й порядок, вторая производная; 3 крайние точки с каждой стороны не используются."""
    c = np.array([1/90, -3/20, 3/2, -49/18, 3/2, -3/20, 1/90]) / h**2
    out = np.zeros_like(y)
    for j, cj in enumerate(c):
        s = j - 3
        out[3:-3] += cj * y[3 + s:len(y) - 3 + s]
    return out


def ansatz(tau, h, corr=True, delta=WIN, use_chi=True):
    """u1(x)=y(x), u2(x)=y(-x) на окне [x0-WIN, x0+WIN] с шагом h; лямбда = tau^2 w."""
    n = int(round(WIN / h))
    x = X0 + h * np.arange(-n, n + 1)
    a, b = a_f(x), np.sqrt(x**2 - 0.25)
    bp = x / b
    E = np.zeros((len(x), 2, 2), complex)
    E[:, 0, 0] = a; E[:, 0, 1] = a; E[:, 1, 0] = 1j * b; E[:, 1, 1] = -1j * b
    E1 = np.zeros_like(E); E1[:, 0, 0] = 1; E1[:, 0, 1] = 1; E1[:, 1, 0] = 1j * bp; E1[:, 1, 1] = -1j * bp
    B = np.linalg.inv(E) @ E1
    rp, rm = 1 / (1 + 1j * b), 1 / (1 - 1j * b)
    b0 = np.sqrt(X0**2 - 0.25)
    sw = np.sqrt((1 + 1j * b0) / abs(1 + 1j * b0))
    rph = np.sqrt(rp)
    dr = -0.5 * rph * 1j * bp / (1 + 1j * b)
    if (sw * dr[n]).imag < 0:
        sw = -sw
    phi2 = (sw * dr[n]).imag
    S = cumulative_trapezoid(rph, x, initial=0); S -= S[n]
    IB = cumulative_trapezoid(B[:, 0, 0], x, initial=0)
    A = (1 + 1j * b) ** 0.25 * np.exp(-IB)
    lam = tau**2 * sw**2
    Z = A * np.exp(1j * tau * sw * S)
    Zp = (1j * tau * sw * rph + 1j * bp / (4 * (1 + 1j * b)) - B[:, 0, 0]) * Z
    v = 2 * B[:, 1, 0] * Zp / (lam * (rp - rm)) if corr else 0 * Z
    u1, u2 = a * (Z + v), 1j * b * (Z - v)
    if use_chi:
        t = (x - X0) / delta
        # срезка: chi = 1 при |t| < 1/2 (ядро пакета не трогаем), гладкий спад на 1/2 < |t| < 1
        f = lambda u: np.where(u > 0, np.exp(-1 / np.maximum(u, 1e-300)), 0.0)
        u = np.clip((np.abs(t) - 0.5) / 0.5, 0, 1)
        chi = 1 - f(u) / (f(u) + f(1 - u))
        u1, u2 = chi * u1, chi * u2
    return x, u1, u2, lam, phi2, n


def resid(tau, h=1e-5, corr=True, delta=WIN, use_chi=True, inner=None):
    """||(L-lam)y|| / ||y||. С chi: по всему окну. Без chi: невязка только при |x-x0|<inner,
    норма y по всему окну (отделяет ВКБ-ошибку от ошибки среза)."""
    x, u1, u2, lam, phi2, n = ansatz(tau, h, corr, delta, use_chi)
    u1pp, u2pp = fd2(u1, h), fd2(u2, h)
    r1 = -u1pp - a_f(x) * u2pp - lam * u1
    r2 = -u2pp - a_f(-x) * u1pp - lam * u2
    mask = np.ones(len(x), bool); mask[:3] = False; mask[-3:] = False
    if inner is not None:
        mask &= np.abs(x - X0) < inner
    num = np.sqrt(h * np.sum((abs(r1)**2 + abs(r2)**2)[mask]))
    den = np.sqrt(h * np.sum(abs(u1)**2 + abs(u2)**2))
    return num / den, phi2, np.sqrt(h * np.sum(abs(u1pp)**2 + abs(u2pp)**2)) / den / tau**2


print("== Часть A: ВКБ-квазимоды, a = x + 1/2, x0 = 3/4 ==")
b0 = np.sqrt(X0**2 - 0.25)
print(f"b(x0) = {b0:.6f}, arg w = arg(1+ib0) = {np.degrees(np.angle(1+1j*b0)):.4f} град")

# K-A1: FD-оператор против аналитического L_a
yt = np.sin(3 * np.pi * XG)
ypp = fd2(yt, H)
exact = (3 * np.pi)**2 * yt + a_f(XG) * (3 * np.pi)**2 * yt[::-1]
errfd = np.max(abs((-ypp - a_f(XG) * ypp[::-1])[10:-10] - exact[10:-10]))
print(f"K-A1: FD-оператор против аналитического L_a на sin(3 pi x): max ошибка {errfd:.2e}")
# K-A2: оконная (U-форма) невязка совпадает с невязкой настоящего L_a на полной сетке (ячейка h=1e-4)
tau = 20
x, u1, u2, lam, phi2, n = ansatz(tau, 1e-4)
y = np.zeros(len(XG), complex)
sl = slice(I0 - n, I0 + n + 1)
y[sl] = u1
yi = np.zeros(len(XG), complex); yi[sl] = u2
y += yi[::-1]
ypp = fd2(y, H)
rr = -ypp - a_f(XG) * ypp[::-1] - lam * y
full = np.sqrt(np.sum(abs(rr[3:-3])**2) / np.sum(abs(y)**2))
print(f"K-A2: tau=20 невязка на полной сетке L_a: {full:.6f}, оконная U-форма: {resid(20, 1e-4)[0]:.6f}")
# K-A3: независимость от шага
print("K-A3: шаг h=2e-5,1e-5,5e-6 при tau=160:", [f"{resid(160, h)[0]:.6f}" for h in (2e-5, 1e-5, 5e-6)])

print("\nI. С срезкой chi (delta=0.2) и с поправкой / без поправки: ||res||/||y||")
print("tau | с поправкой | без (v=0) | с поправкой /tau | без /tau | exp(-tau*phi''*(delta/2)^2/2)")
for tau in (10, 20, 40, 80, 160, 320, 640, 1280, 2560, 5120, 10240, 20480):
    h = min(1e-5, 0.05 / tau)
    r1, phi2, _ = resid(tau, h, True)
    r0, _, _ = resid(tau, h, False)
    print(f"{tau:5d} | {r1:10.4f} | {r0:10.4f} | {r1/tau:9.5f} | {r0/tau:9.5f} | {np.exp(-tau*phi2*(WIN/2)**2/2):.2e}")
print(f"(phi''(x0) = {phi2:.4f})")

print("\nII. Без среза (чистая ВКБ-ошибка): невязка при |x-x0|<0.1, норма y по окну +-0.2")
print("tau | с поправкой | без (v=0) | с поправкой /tau | без /tau")
for tau in (10, 20, 40, 80, 160, 320, 640, 1280, 2560, 5120):
    h = min(1e-5, 0.05 / tau)
    r1, _, _ = resid(tau, h, True, use_chi=False, inner=0.1)
    r0, _, _ = resid(tau, h, False, use_chi=False, inner=0.1)
    print(f"{tau:5d} | {r1:10.4f} | {r0:10.4f} | {r1/tau:9.5f} | {r0/tau:9.5f}")

print("\nIII. Контроль: lambda сдвинута с луча на 0.3 рад (ожидается 0.2955 tau^2)")
for tau in (2560, 5120):
    hh = min(1e-5, 0.05 / tau)
    x, u1, u2, lam, _, n = ansatz(tau, hh)
    lam2 = lam * np.exp(0.3j)
    u1pp, u2pp = fd2(u1, hh), fd2(u2, hh)
    r1 = -u1pp - a_f(x) * u2pp - lam2 * u1; r2 = -u2pp - a_f(-x) * u1pp - lam2 * u2
    q = np.sqrt(np.sum((abs(r1)**2 + abs(r2)**2)[3:-3]) / np.sum(abs(u1)**2 + abs(u2)**2))
    print(f"tau={tau}: {q:.2f}, /tau^2 = {q/tau**2:.4f}")


# ---------------------------------------------------------------- часть B
def cheb(N):
    x = np.cos(np.pi * np.arange(N + 1) / N)
    c = np.hstack([2, np.ones(N - 1), 2]) * (-1) ** np.arange(N + 1)
    X = np.tile(x, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D -= np.diag(D.sum(axis=1))
    return D, x


def clencurt(N):
    theta = np.pi * np.arange(N + 1) / N
    w = np.zeros(N + 1)
    ii = np.arange(1, N)
    v = np.ones(N - 1)
    if N % 2 == 0:
        w[0] = w[N] = 1 / (N**2 - 1)
        for k in range(1, N // 2):
            v -= 2 * np.cos(2 * k * theta[ii]) / (4 * k**2 - 1)
        v -= np.cos(N * theta[ii]) / (N**2 - 1)
    else:
        w[0] = w[N] = 1 / N**2
        for k in range(1, (N - 1) // 2 + 1):
            v -= 2 * np.cos(2 * k * theta[ii]) / (4 * k**2 - 1)
    w[ii] = 2 * v / N
    return w


def pairs_cheb(afun, N):
    D, x = cheb(N)
    D2 = (D @ D)[1:-1, 1:-1]
    xi = x[1:-1]
    L = -(np.eye(N - 1) + np.diag(afun(xi)) @ np.eye(N - 1)[::-1]) @ D2
    w = clencurt(N)[1:-1]
    lam, vl, vr = sla.eig(L, left=True, right=True)
    o = np.argsort(abs(lam))
    lam, vl, vr = lam[o], vl[:, o], vr[:, o]
    ny = np.sqrt(np.einsum('ik,i,ik->k', vr.conj(), w, vr).real)
    nz = np.sqrt(np.einsum('ik,i,ik->k', vl.conj(), 1 / w, vl).real)
    ip = abs(np.einsum('ik,ik->k', vl.conj(), vr))
    kap = ny * nz / ip
    res = np.array([np.linalg.norm(L @ vr[:, k] - lam[k] * vr[:, k]) / np.linalg.norm(vr[:, k]) for k in range(len(lam))])
    return lam, kap, res


def pairs_sine(afun, N, M=4000):
    xq, wq = np.polynomial.legendre.leggauss(M)
    n = np.arange(1, N + 1)
    S = np.sin(np.pi / 2 * np.outer(n, xq + 1))      # s_n(x_q)
    Sr = np.sin(np.pi / 2 * np.outer(n, 1 - xq))     # s_n(-x_q)
    G = (S * (wq * afun(xq))) @ Sr.T                 # int s_m a s_n(-x)
    Lm = (np.eye(N) + G) * (n * np.pi / 2)**2        # (I+G) K
    lam, vl, vr = sla.eig(Lm, left=True, right=True)
    o = np.argsort(abs(lam))
    lam, vl, vr = lam[o], vl[:, o], vr[:, o]
    ny = np.linalg.norm(vr, axis=0); nz = np.linalg.norm(vl, axis=0)
    ip = abs(np.einsum('ik,ik->k', vl.conj(), vr))
    res = np.array([np.linalg.norm(Lm @ vr[:, k] - lam[k] * vr[:, k]) / ny[k] for k in range(N)])
    return lam, ny * nz / ip, res


def match(l1, l2):
    return np.array([abs(l2 - z).min() / abs(z) for z in l1])


print("\n== Часть B: контроль a = 1/2 ==")
half = lambda x: 0.5 + 0 * x
exact = np.sort(np.hstack([1.5 * np.pi**2 * (np.arange(1, 40) - 0.5)**2, 0.5 * np.pi**2 * np.arange(1, 40)**2]))[:40]
for name, fn in (("cheb120", lambda: pairs_cheb(half, 120)), ("cheb180", lambda: pairs_cheb(half, 180)),
                 ("sine120", lambda: pairs_sine(half, 120)), ("sine180", lambda: pairs_sine(half, 180))):
    lam, kap, res = fn()
    print(f"{name}: первые 40: max отн. ошибка lambda {np.max(abs(lam[:40]-exact)/exact):.2e}; "
          f"kappa в k=1..40: min {kap[:40].min():.6f}, max {kap[:40].max():.6f}; "
          f"невязка max {res[:40].max():.1e}")

print("\n== Часть B: a = x + 1/2 ==")
R = {}
for name, fn in (("cheb120", lambda: pairs_cheb(a_f, 120)), ("cheb180", lambda: pairs_cheb(a_f, 180)),
                 ("sine120", lambda: pairs_sine(a_f, 120)), ("sine180", lambda: pairs_sine(a_f, 180))):
    R[name] = fn()
    print(f"{name}: готово, t = {time.time()-T0:.1f} c")
lc, kc, rc = R["cheb180"]
d_c = match(lc, R["cheb120"][0])
d_s = match(lc, R["sine180"][0])


def kap_at(name, z):
    l, k, _ = R[name]
    return k[np.argmin(abs(l - z))]


print("\n k | lambda_k (cheb180)         | отн.расх. c120 | отн.расх. sine180 | kappa c120 | kappa c180 | kappa s120 | kappa s180 | невязка c180")
for k in list(range(0, 20)) + list(range(20, 100, 5)):
    z = lc[k]
    print(f"{k+1:3d} | {z.real:11.4f}{z.imag:+11.4f}i | {d_c[k]:.1e} | {d_s[k]:.1e} | "
          f"{kap_at('cheb120', z):.4g} | {kc[k]:.4g} | {kap_at('sine120', z):.4g} | {kap_at('sine180', z):.4g} | {rc[k]:.1e}")
print("\nПодгонка log kappa по k (пары, где cheb120, cheb180 и sine180 совпадают по lambda лучше 1e-8)")
ok = np.where((d_c < 1e-8) & (d_s < 1e-8))[0]
cplx = ok[abs(lc[ok].imag) > 1e-6 * abs(lc[ok])]
cplx = cplx[cplx >= 10]
kk = cplx + 1
ly = np.log(kc[cplx])
p1 = np.polyfit(kk, ly, 1); r1 = ly - np.polyval(p1, kk)
p2 = np.polyfit(np.log(kk), ly, 1); r2 = ly - np.polyval(p2, np.log(kk))
print(f"k от {kk.min()} до {kk.max()} ({len(kk)} собств. значений): log kappa = {p1[0]:.4f} k + {p1[1]:.3f} "
      f"(СКО остатка {r1.std():.3f}); степенной kappa ~ k^{p2[0]:.2f} (СКО остатка {r2.std():.3f})")
sq = np.sqrt(abs(lc[cplx]))
p3 = np.polyfit(sq, ly, 1); r3 = ly - np.polyval(p3, sq)
print(f"log kappa = {p3[0]:.4f} sqrt|lambda| + {p3[1]:.3f} (СКО остатка {r3.std():.3f})")
print(f"Последняя пара с совпадением lambda < 1e-8: k = {ok.max()+1}")
ok2 = np.where(d_s < 1e-6)[0]
c2 = ok2[(abs(lc[ok2].imag) > 1e-6 * abs(lc[ok2])) & (ok2 >= 10)]
k2 = c2 + 1; l2 = np.log(kc[c2])
q1 = np.polyfit(k2, l2, 1); s1 = (l2 - np.polyval(q1, k2)).std()
q2 = np.polyfit(np.log(k2), l2, 1); s2 = (l2 - np.polyval(q2, np.log(k2))).std()
print(f"Расширенный диапазон (cheb180 и sine180 совпадают по lambda лучше 1e-6): k от {k2.min()} до {k2.max()}: "
      f"log kappa = {q1[0]:.4f} k + {q1[1]:.3f} (СКО {s1:.3f}); степенной k^{q2[0]:.2f} (СКО {s2:.3f})")
big = [k for k in range(10, 80, 5) if k in set(c2)]
print("kappa(k+5)/kappa(k) по комплексным парам:", [f"{kc[k+5]/kc[k]:.2f}" for k in big if k + 5 in set(c2)])
print("kappa cheb180 против sine180, k<=75: max отн. расхождение",
      max(abs(kc[k] - kap_at('sine180', lc[k])) / kc[k] for k in range(75)))
print(f"\nвремя: {time.time()-T0:.1f} c")
