# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E1 (узел I22): нормы сумм спектральных проекторов для a = 1/2 + x/4 и a = 1/2 + x/3.

Вопрос (критика I22 от 14.10.2026):
  найти первые 200 значений lambda коллокацией, сгруппировать sqrt(lambda) с порогом 0.05,
  посчитать || sum_{s in Phi} P_s ||_{L2 -> L2} и || sum_{s in Phi} P_s ||_{L2 -> H01}
  для 500 случайных наборов Phi.
  По описанию критика: рост второй нормы опровергает шаг 6 идеи I22, рост первой — вывод (C).

== Что именно считается ==

L_a y = -y''(x) - a(x) y''(-x) на (-1,1), y(+-1) = 0.

Метод 1 (модельный оператор T из пункта (A) идеи I22, точные функции).
T = M_r(L_b - Q)M_r^{-1}, где b = sigma_a sqrt(a(x)a(-x)), sigma_+- = 1 +- b, m_+- = sigma_+-^{1/4},
S_+-' = sigma_+-^{-1/2}, l_+- = S_+-(1), q_+- = -sigma_+- m_+-''/m_+-, Q = q_+ P_+ + q_- P_-,
P_+- = (1 +- R)/2. Собственные функции T и его собственные значения:
    f^+_n = r m_+ cos(nu^+_n S_+),  nu^+_n = pi(2n-1)/(2 l_+),  lambda = (nu^+_n)^2   (чётные);
    f^-_n = r m_- sin(nu^-_n S_-),  nu^-_n = pi n / l_-,      lambda = (nu^-_n)^2   (нечётные).
(В идее записано nu^+_n = pi(n-1/2)/l_+ — то же самое: cos(pi(n-1/2)S/l_+) =
cos(pi(2n-1)S/(2l_+)). При b = 1/2 (случай a = 1/2) l_+ = sqrt(2/3), l_- = sqrt(2), и значения
совпадают с точным спектром C3: (3/2)pi^2(n-1/2)^2 и (1/2)pi^2 n^2.)
Группы: соседние по возрастанию nu с зазором < 0.05. Для группы функций (значения и производные
на равномерной сетке) считаются матрицы Грама
    G_ij = int f_i f_j dx,  G^rho_ij = int f_i f_j sigma^{-1/2} dx,  H_ij = int f'_i f'_j dx,
и нормы проектора Рисса на оболочку группы вдоль двойственного базиса
    ||P_s||_{L2->L2}  = sqrt(lambda_max(G^{-1} G^rho)),
    ||P_s||_{L2->H01} = sqrt(lambda_max(G^{-1} H)).
Для набора Phi матрицы Грама складываются по группам. Расчёт точен до квадратуры
(Симпсон, 4096 интервалов; устойчивость проверяется на 2048 и 8192).

Метод 2 (коллокация, буквально по заданию): A = (I + diag(a(t))R)(-D2) на внутренних узлах
Чебышёва-Лобатто; собственные пары z_j (A z = lambda z), v_j (v^H A = lambda v^H),
нормировка V_j = conj(v_j^H z_j)/|v_j^H z_j|^2 v_j (так что V^H Z = I), проектор группы
P = Z_I V_I^T; нормы sigma_max(P) и sigma_max(D_внутр P) в дискретном L2 с весами
Кленшоу-Кёртиса. Для несамосопряжённого L_a этот путь чувствителен к смешиванию близких
собственных функций и к нормировке двойственного базиса: см. контроль K1/K4.

Контроль метода:
  (K0) коллокация: D sin(mx) при N = 12; ||u||_w и H01-полунорма для cos(pi x/2) и sin(pi x);
       систематика дискретной H01-полунормы на высоких модах (m до 200, N до 800).
  (K1) a = 1/2 (известный ответ, C3): точный спектр (3/2)pi^2(n-1/2)^2 и (1/2)pi^2 m^2;
       частоты (A); нормы одиночных проекторов равны 1 (проектор на одну собственную функцию).
  (K2) квадратуры: l_+- по Симпсону при M = 4096, 8192 и по scipy.integrate.quad; сверка с
       данными критики (a = 1/2 + x/10: 0.81741209, 1.40951336) и с точным sqrt(2/3), sqrt(2).
  (K3) модельный оператор: невязка (L_b - Q)f - nu^2 f на явных функциях (A).
  (K4) независимая дискретизация (конечные разности на мелкой сетке) для той же задачи:
       показывает, что T != L_a (расхождение первых собственных значений ~ процентов) и
       даёт контрольные значения для коллокации.
Параметры и зёрна фиксированы в коде. Таблицы — в stdout и data/run.log, массивы — data/*.npz.
"""

import json
import math
import os
import time

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from scipy.integrate import quad
from scipy.integrate import simpson as scipy_simpson

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)

EPS_GROUP = 0.05          # порог группировки nu (задание критика)
KMAX = 200                # число значений lambda
NSETS = 500               # число случайных наборов Phi
SEED = 20261014           # зерно генератора случайных наборов
N_LIST = (240, 400, 600)  # разрешения коллокации
N_MAIN = 600              # основное разрешение коллокации
M_GRID = 1 << 12          # интервалов Симпсона в методе 1

LOG = []


def say(*parts):
    line = " ".join(str(p) for p in parts)
    print(line, flush=True)
    LOG.append(line)


def table(header, rows):
    if not rows:
        return
    widths = [max(len(str(header[j])), *(len(str(r[j])) for r in rows))
              for j in range(len(header))]
    say("  " + "  ".join(str(header[j]).ljust(widths[j]) for j in range(len(header))))
    for r in rows:
        say("  " + "  ".join(str(r[j]).ljust(widths[j]) for j in range(len(header))))


# ---------------------------------------------------------------- коллокация


def cheb(N):
    """Узлы Чебышёва-Лобатто и матрица дифференцирования D (метод odd_check.py)."""
    k = np.arange(N + 1)
    t = np.cos(np.pi * k / N)
    c = np.ones(N + 1)
    c[0] = 2
    c[-1] = 2
    c = c * (-1.0) ** k
    X = np.tile(t, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D = D - np.diag(D.sum(axis=1))
    return D, t


def clenshaw_curtis(N):
    """Веса Кленшоу-Кёртиса на узлах Чебышёва-Лобатто."""
    k = np.arange(N + 1)
    theta = np.pi * k / N
    w = np.zeros(N + 1)
    v = np.ones(N - 1)
    ii = np.arange(1, N)
    if N % 2 == 0:
        w[0] = w[N] = 1 / (N**2 - 1)
        for j in range(1, N // 2):
            v -= 2 * np.cos(2 * j * theta[ii]) / (4 * j**2 - 1)
        v -= np.cos(N * theta[ii]) / (N**2 - 1)
    else:
        w[0] = w[N] = 1 / N**2
        for j in range(1, (N - 1) // 2 + 1):
            v -= 2 * np.cos(2 * j * theta[ii]) / (4 * j**2 - 1)
    w[ii] = 2 * v / N
    return w


def build(N, a_fun):
    """Коллокационная матрица A и данные дискретизации."""
    D, t = cheb(N)
    ti = t[1:-1]
    Dint = D[1:-1, 1:-1]
    D2 = (D @ D)[1:-1, 1:-1]
    w = clenshaw_curtis(N)[1:-1]
    R = np.eye(N - 1)[::-1]
    A = (np.eye(N - 1) + np.diag(a_fun(ti)) @ R) @ (-D2)
    return dict(N=N, t=ti, D=Dint, D2=D2, w=w, R=R, A=A)


def eigens(d):
    """Спектр: правые z_j и левые v_j по возрастанию |lambda| (|lambda| < 1e-9 отброшены)."""
    lam, VL, VR = la.eig(d["A"], left=True, right=True)
    order = np.argsort(np.abs(lam))
    lam, VL, VR = lam[order], VL[:, order], VR[:, order]
    keep = np.where(np.abs(lam) > 1e-9)[0]
    return lam[keep], VL[:, keep], VR[:, keep]


def l2w(w, v):
    return float(np.sqrt(np.sum(w * np.abs(v) ** 2)))


def h1w(w, D, v):
    return float(np.sqrt(np.sum(w * np.abs(D @ v) ** 2)))


def duals(VL, VR):
    """V_j = conj(v_j^H z_j)/|v_j^H z_j|^2 * v_j, так что V^H Z = I.

    Тогда W_j = conj(V_j) двойствен к z_j по <-,->_w и проектор группы есть P = Z_I V_I^T.
    Внимание: в output/ideas/split_check.py стояло W = VL / w — это не нормировка
    (у к о м п л е к с н ы х пар <v,z> ~ 1e-8, и нормы проекторов там завышены).
    """
    inner = np.einsum("ij,ij->j", VL.conj(), VR)          # v_j^H z_j
    if np.abs(inner).min() < 1e-12:
        raise RuntimeError("вырожденная биортогонализация")
    return VL * (inner.conj() / np.abs(inner) ** 2)[None, :]


def proj_GM(d, Z, V, idx):
    P = Z[:, idx] @ V[:, idx].T
    return P, d["D"] @ P


def proj_norms(d, Z, V, idx, exact=True):
    P, DP = proj_GM(d, Z, V, idx)
    if exact:
        return float(la.svdvals(P)[0]), float(la.svdvals(DP)[0])
    rng = np.random.default_rng(SEED + 17 * len(idx) + int(idx[0]))
    G = rng.standard_normal((P.shape[1], 3)) + 1j * rng.standard_normal((P.shape[1], 3))
    return (float(np.linalg.norm(P @ G, axis=0).max()),
            float(np.linalg.norm(DP @ G, axis=0).max()))


def residual(d, z, lam):
    r = d["A"] @ z - lam * z
    return float(np.linalg.norm(r) / (la.norm(d["A"] @ z) + abs(lam) * la.norm(z)))


# ---------------------------------------------------------------- модель Лиувилля


def simp_cumul(f, xs):
    """Кумулятивные интегралы Симпсона от xs[0] до xs[k] (число интервалов чётно)."""
    n = len(xs) - 1
    h = xs[1] - xs[0]
    s = np.zeros(n + 1)
    cur = 0.0
    for i in range(0, n - 1, 2):
        step = h * (f[i] + 4 * f[i + 1] + f[i + 2]) / 3
        s[i + 1] = cur + step / 2
        s[i + 2] = cur + step
        cur += step
    return s


def cum_from_zero(f, xs):
    """int_0^x f по Симпсону на симметричной равномерной сетке (x = 0 в сетке отсутствует).

    Сетка симметрична, f(x) = f(-x): int_0^{xs[half+i]} = int_0^{i h}, а узлы
    xs[half], xs[half+1], ... отвечают точкам 0, h, 2h, ...; xr = -xs[half:][::-1].
    """
    M = len(xs) - 1
    half = M // 2
    xr = -xs[half:][::-1]                 # 0, h, 2h, ..., 1
    fr = f[half:][::-1]
    sr = simp_cumul(fr, xr)
    out = np.concatenate([-sr[:0:-1], sr])       # узлы -1 ... -h, 0, h ... 1
    return out, float(xs[half])


def model_params(a_fun, M=M_GRID):
    """b, sigma_+- , m_+-, S_+-, l_+-, q_+- на симметричной равномерной сетке (M чётно)."""
    xs = np.linspace(-1.0, 1.0, M + 1)
    a = a_fun(xs)
    b = np.sign(a) * np.sqrt(np.abs(a * a[::-1]))
    sig_p, sig_m = 1 + b, 1 - b
    m_p, m_m = sig_p ** 0.25, sig_m ** 0.25
    Sp, x0 = cum_from_zero(sig_p ** (-0.5), xs)
    Sm, _ = cum_from_zero(sig_m ** (-0.5), xs)
    h = xs[1] - xs[0]

    def d1(f):
        out = np.zeros_like(f)
        out[2:-2] = (f[:-4] - 8 * f[1:-3] + 8 * f[3:-1] - f[4:]) / (12 * h)
        out[1] = (f[2] - f[0]) / (2 * h)
        out[-2] = (f[-1] - f[-3]) / (2 * h)
        out[0] = out[1]
        out[-1] = out[-2]
        return out

    def d2(f):
        out = np.zeros_like(f)
        out[2:-2] = (-f[4:] + 16 * f[3:-1] - 30 * f[2:-2] + 16 * f[1:-3] - f[:-4]) / (12 * h**2)
        out[1] = (f[2] - 2 * f[1] + f[0]) / h**2
        out[-2] = (f[-1] - 2 * f[-2] + f[-3]) / h**2
        out[0] = out[1]
        out[-1] = out[-2]
        return out

    q_p = -sig_p * d2(m_p) / m_p
    q_m = -sig_m * d2(m_m) / m_m
    return dict(xs=xs, h=h, x0=x0, a=a, b=b, sig_p=sig_p, sig_m=sig_m, m_p=m_p, m_m=m_m,
                Sp=Sp, Sm=Sm, q_p=q_p, q_m=q_m, d1=d1, d2=d2,
                l_p=float(Sp[-1]), l_m=float(Sm[-1]))


def model_nu(ncount, l_p, l_m):
    """Первые ncount частот объединения двух серий, по возрастанию, и признак серии."""
    n = np.arange(1, ncount + 1)
    nu_p = np.pi * (2 * n - 1) / (2 * l_p)
    nu_m = np.pi * n / l_m
    allnu = np.concatenate([nu_p, nu_m])
    kind = np.concatenate([np.ones(ncount, dtype=int), -np.ones(ncount, dtype=int)])
    order = np.argsort(allnu)[:ncount]
    return allnu[order], nu_p, nu_m, kind[order]


def cluster(vals, eps):
    """Группы соседних (по возрастанию) значений на расстоянии < eps."""
    v = np.sort(np.asarray(vals, dtype=float))
    groups = [[0]]
    for i in range(1, len(v)):
        if v[i] - v[i - 1] < eps:
            groups[-1].append(i)
        else:
            groups.append([i])
    return groups, v


def exact_basis(a_fun, ncount, M=M_GRID):
    """Значения и производные явных функций модели на равномерной сетке (Симпсон)."""
    mp = model_params(a_fun, M)
    xs = mp["xs"]
    r = np.sqrt(np.abs(mp["a"]))
    F, dF, nus, kinds = [], [], [], []
    n = np.arange(1, ncount + 1)
    for nu in np.pi * (2 * n - 1) / (2 * mp["l_p"]):
        f = r * mp["m_p"] * np.cos(nu * mp["Sp"])
        F.append(f)
        dF.append(mp["d1"](f))
        nus.append(nu)
        kinds.append(1)
    for nu in np.pi * n / mp["l_m"]:
        f = r * mp["m_m"] * np.sin(nu * mp["Sm"])
        F.append(f)
        dF.append(mp["d1"](f))
        nus.append(nu)
        kinds.append(-1)
    nus = np.array(nus)
    kinds = np.array(kinds)
    order = np.argsort(nus)[:ncount]
    h = xs[1] - xs[0]
    w = np.ones(len(xs))
    w[1:-1:2] = 4.0
    w[2:-1:2] = 2.0
    w *= h / 3
    return dict(xs=xs, mp=mp, xs_w=w, F=np.array(F)[order], dF=np.array(dF)[order],
                nu=nus[order], kind=kinds[order])


# ================================================================ K0


say("=" * 100)
say("K0. Контроль дискретизации коллокации")
say("=" * 100)
D12, t12 = cheb(12)
for m in (1, 2, 3, 7):
    err = np.abs(D12 @ np.sin(m * t12) - m * np.cos(m * t12)).max()
    say(f"  N = 12: max|D sin({m}x) - {m}cos({m}x)| = {err:.2e}")
d_ref = build(N_MAIN, lambda x: 0.5 + x / 4)
for lab, f, exact in (("cos(pi x/2)", np.cos(np.pi * d_ref["t"] / 2), np.pi / 2),
                      ("sin(pi x)", np.sin(np.pi * d_ref["t"]), np.pi)):
    say(f"  N = {N_MAIN}, u = {lab:12s}: ||u||_w = {l2w(d_ref['w'], f):.10f} (точно 1),"
        f" H01-полунорма = {h1w(d_ref['w'], d_ref['D'], f):.10f} (точно {exact:.10f})")
say("  дискретная H01-полунорма/||f||_w для f = sin(m pi x) (систематика метода 2):")
rows = []
for N in (240, 400, 600, 800):
    dd = build(N, lambda x: np.full_like(x, 0.5))
    for m in (1, 25, 100, 200):
        f = np.sin(m * np.pi * dd["t"])
        val = h1w(dd["w"], dd["D"], f) / l2w(dd["w"], f)
        rows.append((N, m, f"{val:.6f}", f"{m*np.pi:.4f}", f"{val/(m*np.pi)-1:+.2e}"))
table(["N", "m", "H01-полунорма/||f||_w", "точное m*pi", "отн. отклонение"], rows)

# ================================================================ K2


say("")
say("=" * 100)
say("K2. Контроль квадратуры: длины Лиувилля l_+-")
say("=" * 100)
CASES = {
    "a = 1/2 (контроль)": (lambda x: np.full_like(x, 0.5), math.sqrt(2 / 3), math.sqrt(2)),
    "a = 1/2 + x/4": (lambda x: 0.5 + x / 4, None, None),
    "a = 1/2 + x/3": (lambda x: 0.5 + x / 3, None, None),
    "a = 1/2 + x/10": (lambda x: 0.5 + x / 10, 0.81741209, 1.40951336),
}
K2 = {}
for name, (af, ex_p, ex_m) in CASES.items():
    vals = []
    for M in (1 << 12, 1 << 13):
        mp = model_params(af, M)
        vals.append((mp["l_p"], mp["l_m"]))
    b_fun = lambda x: math.sqrt(abs(af(np.array([x]))[0] * af(np.array([-x]))[0]))
    qp = quad(lambda x: (1 + b_fun(x)) ** (-0.5), 0, 1, epsabs=1e-14, limit=200)[0]
    qm = quad(lambda x: (1 - b_fun(x)) ** (-0.5), 0, 1, epsabs=1e-14, limit=200)[0]
    K2[name] = dict(simpson=vals, quad=(qp, qm), exact=(ex_p, ex_m))
    txt = (f"  {name:20s} l_+ = {vals[1][0]:.9f} (M=4096: {vals[0][0]:.9f}, quad: {qp:.9f});"
           f"  l_- = {vals[1][1]:.9f} (M=4096: {vals[0][1]:.9f}, quad: {qm:.9f})")
    if ex_p is not None:
        txt += f";  эталон {ex_p:.9f}, {ex_m:.9f}"
    say(txt)
    say(f"      |M=4096 - M=8192|: {abs(vals[0][0]-vals[1][0]):.2e} и"
        f" {abs(vals[0][1]-vals[1][1]):.2e}; |M=8192 - quad|:"
        f" {abs(vals[1][0]-qp):.2e} и {abs(vals[1][1]-qm):.2e}")

# ================================================================ K3


def model_identity_residual(mp, nu_list):
    """Невязка (L_b - Q) f - nu^2 f на явных функциях: на своей чётности L_b f = -sigma_+- f''
    и Q f = q_+- f."""
    r = np.sqrt(np.abs(mp["a"]))
    d2 = mp["d2"]
    res = []
    for nu, kind in nu_list:
        if kind > 0:
            f = r * mp["m_p"] * np.cos(nu * mp["Sp"])
            rho = -mp["sig_p"] * d2(f) - mp["q_p"] * f - nu**2 * f
        else:
            f = r * mp["m_m"] * np.sin(nu * mp["Sm"])
            rho = -mp["sig_m"] * d2(f) - mp["q_m"] * f - nu**2 * f
        scale = nu**2 * np.abs(f).max() + np.abs(np.abs(mp["a"]) * d2(f)).max()
        res.append(float(np.abs(rho[2:-2]).max() / scale))
    return res


say("")
say("=" * 100)
say("K3. Контроль модели: невязка (L_b - Q)f - nu^2 f, a = 1/2 + x/10")
say("=" * 100)
a_k3 = lambda x: 0.5 + x / 10
mp_k3 = model_params(a_k3, 1 << 13)
say(f"  l_+ = {mp_k3['l_p']:.8f} (критика I22: 0.81741209),"
    f" l_- = {mp_k3['l_m']:.8f} (1.40951336)")
nu_k3, nu_p3, nu_m3, kind_k3 = model_nu(KMAX, mp_k3["l_p"], mp_k3["l_m"])
res_k3 = model_identity_residual(mp_k3, [(nu_p3[0], 1), (nu_p3[4], 1), (nu_p3[19], 1),
                                         (nu_m3[0], -1), (nu_m3[4], -1), (nu_m3[19], -1)])
say("  отн. невязки на функциях (A): " + ", ".join(f"{r:.2e}" for r in res_k3))
for M in (1 << 12, 1 << 13, 1 << 14):
    mp2 = model_params(a_k3, M)
    r2 = model_identity_residual(mp2, [(nu_p3[0], 1), (nu_p3[19], 1), (nu_m3[19], -1)])
    say(f"  M = {M:6d}: невязки " + ", ".join(f"{r:.2e}" for r in r2))

# ================================================================ K4


say("")
say("=" * 100)
say("K4. Независимая дискретизация: конечные разности, первые lambda")
say("=" * 100)
say("  (в чётном и нечётном канале L_a при нечётной части a не сохраняет чётность, поэтому")
say("   сравниваются две вещи: точный спектр L_a из мелкой сетки и частоты модели T.)")


def fd_spectrum(a_fun, N, k=3):
    """Первые k собственных значений L_a на мелкой сетке (коллокация Чебышёва высокого N)."""
    d = build(N, a_fun)
    lam, VL, VR = eigens(d)
    mu = np.abs(np.sqrt(lam[:KMAX]))
    return np.sort(mu)[:k]


rows = []
for N in (400, 800, 1600):
    mu = fd_spectrum(lambda x: 0.5 + x / 4, N, 4)
    rows.append((N, "  ".join(f"{v:.6f}" for v in mu)))
table(["N", "первые |sqrt(lam)| коллокации"], rows)
mp_p1 = model_params(lambda x: 0.5 + x / 4, 1 << 13)
nu_p1, _, _, _ = model_nu(4, mp_p1["l_p"], mp_p1["l_m"])
say(f"  модель T (вес 1 +- b): первые sqrt(lambda) = "
    + ", ".join(f"{v:.6f}" for v in nu_p1))
say(f"  разность модели и коллокации N = 1600: "
    + ", ".join(f"{abs(a-b):.4f}" for a, b in zip(nu_p1, fd_spectrum(lambda x: 0.5 + x / 4, 1600, 4))))
# невязка явных функций модели при подстановке в L_a (a = 1/2 + x/10): T != L_a
d5 = build(N_MAIN, a_k3)
say("  подстановка функций модели в L_a (нужна, чтобы отделить T от L_a):")
rows = []
for nu, kind in ((nu_p3[0], 1), (nu_m3[0], -1)):
    if kind > 0:
        f = np.sqrt(np.abs(mp_k3["a"])) * mp_k3["m_p"] * np.cos(nu * mp_k3["Sp"])
        sig, q = mp_k3["sig_p"], mp_k3["q_p"]
    else:
        f = np.sqrt(np.abs(mp_k3["a"])) * mp_k3["m_m"] * np.sin(nu * mp_k3["Sm"])
        sig, q = mp_k3["sig_m"], mp_k3["q_m"]
    rho = (-sig * mp_k3["d2"](f) - q * f - nu**2 * f)
    scale = nu**2 * np.abs(f).max() + np.abs(np.abs(mp_k3["a"]) * mp_k3["d2"](f)).max()
    rows.append(("a=1/2+x/10", f"{nu:.4f}", f"{float(np.abs(rho[2:-2]).max()/scale):.3e}"))
table(["коэффициент", "nu", "отн. невязка (L_b - Q)f - nu^2 f"], rows)

# ================================================================ метод 1


def analyse_exact(tag, a_fun):
    say("")
    say("=" * 100)
    say(f"МЕТОД 1 (явные функции модельного оператора T): {tag}")
    say("=" * 100)
    t_start = time.time()
    B = exact_basis(a_fun, KMAX)
    xs, mp = B["xs"], B["mp"]
    F, dF, nu, wq = B["F"], B["dF"], B["nu"], B["xs_w"]
    sig = mp["sig_p"]                        # 1 + b; у sigma_- = 1 - b тот же вес 1 - b^2
    say(f"  l_+ = {mp['l_p']:.9f}   l_- = {mp['l_m']:.9f}   l_+/l_- = {mp['l_p']/mp['l_m']:.9f}")
    prod = mp["a"] * mp["a"][::-1]
    say(f"  b в [{mp['b'].min():.6f}, {mp['b'].max():.6f}];  a(x)a(-x) в"
        f" [{prod.min():.6f}, {prod.max():.6f}]")
    say(f"  узлов квадратуры {len(xs)} (M = {M_GRID}), nu от {nu[0]:.4f} до {nu[-1]:.4f}")
    nrm = np.sqrt(np.einsum("ij,j,ij->i", F, wq, F))
    F, dF = F / nrm[:, None], dF / nrm[:, None]
    chk = np.einsum("ij,j,ij->i", F, wq, F)
    say(f"  ||f_j||_L2 после нормировки: от {chk.min():.6f} до {chk.max():.6f}")
    grp, _ = cluster(nu, EPS_GROUP)
    sizes = {}
    for g in grp:
        sizes[len(g)] = sizes.get(len(g), 0) + 1
    say(f"  группировка nu (eps = {EPS_GROUP}): групп {len(grp)}, размеры"
        f" {dict(sorted(sizes.items()))}")
    big = [(i, len(g), float(nu[g[0]]), float(nu[g[-1]] - nu[g[0]]))
           for i, g in enumerate(grp) if len(g) > 1]
    for i, sz, v0, wd in big[:8]:
        say(f"     группа {i+1:4d}: {sz} значений, начиная с {v0:.4f}, ширина {wd:.4f}")
    G_all = (F * wq[None, :]) @ F.T
    Grho_all = (F * (wq / sig)[None, :]) @ F.T
    H_all = (dF * wq[None, :]) @ dF.T
    say(f"  ||G - I||_max = {np.abs(G_all - np.eye(KMAX)).max():.2e};"
        f" время {time.time()-t_start:.1f} c")

    def norms_of(groups):
        idx = np.concatenate([np.asarray(g) for g in groups])
        if idx.size == 1:
            j = int(idx[0])
            return (math.sqrt(max(Grho_all[j, j] / G_all[j, j], 0.0)),
                    math.sqrt(max(H_all[j, j] / G_all[j, j], 0.0)))
        ixx = np.ix_(idx, idx)
        G = G_all[ixx]
        return (math.sqrt(max(la.eigvalsh(Grho_all[ixx], G, check_finite=False).max(), 0.0)),
                math.sqrt(max(la.eigvalsh(H_all[ixx], G, check_finite=False).max(), 0.0)))

    say("  нормы одиночных функций:")
    rows = []
    for j in (0, 1, 2, 4, 24, 99, 199):
        n2, nh = norms_of([[j]])
        rows.append((j + 1, f"{nu[j]:8.3f}", f"{n2:.6f}", f"{nh:9.3f}", f"{nh/nu[j]:.3f}"))
    table(["j", "nu_j", "||P_j||_L2", "||P_j||_H01", "H01/nu_j"], rows)
    say("  (одиночная функция: ||P_j||_L2 = ||f_j||_rho/||f_j||_L2; ||P_j||_H01 = ||f_j'||/||f_j||)")
    single = []
    for i, g in enumerate(grp):
        n2, nh = norms_of([g])
        single.append((i + 1, len(g), float(nu[g[0]]), n2, nh))
    ws = sorted(single, key=lambda r: -r[3])
    say(f"  нормы групп: ||P_s||_L2 min {min(r[3] for r in single):.6f},"
        f" медиана {np.median([r[3] for r in single]):.6f},"
        f" max {max(r[3] for r in single):.6f}")
    say(f"               ||P_s||_H01 min {min(r[4] for r in single):.3f},"
        f" медиана {np.median([r[4] for r in single]):.3f},"
        f" max {max(r[4] for r in single):.3f}")
    table(["группа", "размер", "nu", "||P_s||_L2", "||P_s||_H01", "H01/nu"],
          [(r[0], r[1], f"{r[2]:8.3f}", f"{r[3]:.6f}", f"{r[4]:9.3f}", f"{r[4]/r[2]:.3f}")
           for r in ws[:5]])
    table(["группа", "размер", "nu", "||P_s||_L2", "||P_s||_H01", "H01/nu"],
          [(r[0], r[1], f"{r[2]:8.3f}", f"{r[3]:.6f}", f"{r[4]:9.3f}", f"{r[4]/r[2]:.3f}")
           for r in ws[-3:]])
    # пары с близкими nu: вклад в нормы
    say("  пары групп размера 2 (близкие nu):")
    rows = []
    for i, g in enumerate(grp):
        if len(g) == 2:
            n2, nh = norms_of([g])
            rows.append((i + 1, f"{nu[g[0]]:.4f}", f"{nu[g[1]]-nu[g[0]]:.5f}",
                         f"{n2:.6f}", f"{nh:.3f}"))
    table(["группа", "nu", "зазор", "||P_s||_L2", "||P_s||_H01"], rows)

    rng = np.random.default_rng(SEED)
    G = len(grp)
    sets = []
    for _ in range(NSETS):
        k = int(rng.integers(1, G + 1))
        pick = rng.choice(G, size=k, replace=False)
        n2, nh = norms_of([grp[s] for s in pick])
        sets.append(dict(k=k, size=int(sum(len(grp[s]) for s in pick)), n2=n2, nh=nh,
                         imax=float(max(nu[j] for s in pick for j in grp[s]))))
    kk = np.array([s["k"] for s in sets])
    ii = np.array([s["size"] for s in sets])
    a2 = np.array([s["n2"] for s in sets])
    ah = np.array([s["nh"] for s in sets])
    im = np.array([s["imax"] for s in sets])
    say("")
    say(f"  {NSETS} случайных наборов Phi (зерно {SEED}), группы по nu модели:")
    say(f"    |Phi| от {ii.min()} до {ii.max()} функций; nu_max от {im.min():.3f} до {im.max():.3f}")
    say(f"    ||P_Phi||_L2 : min {a2.min():.6f}, медиана {np.median(a2):.6f},"
        f" среднее {a2.mean():.6f}, max {a2.max():.6f}")
    say(f"    ||P_Phi||_H01: min {ah.min():.3f}, медиана {np.median(ah):.3f},"
        f" среднее {ah.mean():.3f}, max {ah.max():.3f}")
    say(f"    наклон ||P||_L2: по |Phi| {np.polyfit(ii, a2, 1)[0]:+.6f},"
        f" по числу групп {np.polyfit(kk, a2, 1)[0]:+.6f},"
        f" log-log по nu_max {np.polyfit(np.log(im), np.log(a2), 1)[0]:+.4f}")
    say(f"    наклон log||P||_H01 по log nu_max:"
        f" {np.polyfit(np.log(im), np.log(ah), 1)[0]:.4f}")
    bins = [(1, 10), (11, 25), (26, 50), (51, 100), (101, 150), (151, 200)]
    rows = []
    for lo, hi in bins:
        m = (kk >= lo) & (kk <= hi)
        if not m.any():
            continue
        rows.append((f"{lo}-{hi}", int(m.sum()), f"{a2[m].mean():.6f}", f"{a2[m].max():.6f}",
                     f"{ah[m].mean():.3f}", f"{ah[m].max():.3f}", f"{im[m].mean():.2f}"))
    table(["групп", "наборов", "сред. ||P||_L2", "макс. ||P||_L2", "сред. ||P||_H01",
           "макс. ||P||_H01", "сред. nu_max"], rows)
    say("    нарастающие наборы (первые m групп):")
    rows = []
    for m in sorted({1, 5, 10, 20, 40, 60, 100, 150, G}):
        if m > G:
            continue
        n2, nh = norms_of(grp[:m])
        rows.append((m, int(sum(len(g) for g in grp[:m])), f"{nu[grp[m-1][-1]]:.3f}",
                     f"{n2:.6f}", f"{nh:.3f}", f"{nh/nu[grp[m-1][-1]]:.3f}"))
    table(["m групп", "функций", "nu_max", "||P||_L2", "||P||_H01", "H01/nu_max"], rows)
    say("    устойчивость по сетке квадратуры (нарастающие наборы):")
    rows = []
    for Mtest in (1 << 11, 1 << 12, 1 << 13):
        B2 = exact_basis(a_fun, KMAX, Mtest)
        wq2, sig2 = B2["xs_w"], B2["mp"]["sig_p"]
        F2, dF2 = B2["F"], B2["dF"]
        nrm2 = np.sqrt(np.einsum("ij,j,ij->i", F2, wq2, F2))
        F2, dF2 = F2 / nrm2[:, None], dF2 / nrm2[:, None]
        grp2, _ = cluster(B2["nu"], EPS_GROUP)
        row = [Mtest, len(grp2)]
        for m in (10, 40, 100, 200):
            idx = np.concatenate([np.asarray(g) for g in grp2[:m]])
            Fg, dFg = F2[idx], dF2[idx]
            Gg = (Fg * wq2[None, :]) @ Fg.T
            Gg_r = (Fg * (wq2 / sig2)[None, :]) @ Fg.T
            Hg = (dFg * wq2[None, :]) @ dFg.T
            row += [f"{math.sqrt(max(la.eigvalsh(Gg_r, Gg).max(), 0.0)):.6f}",
                    f"{math.sqrt(max(la.eigvalsh(Hg, Gg).max(), 0.0)):.3f}"]
        rows.append(tuple(row))
    table(["M", "групп"] + [f"m={m}: L2" for m in (10, 40, 100, 200)]
          + [f"m={m}: H01" for m in (10, 40, 100, 200)], rows)
    say(f"  время метода 1: {time.time()-t_start:.1f} c")
    np.savez(os.path.join(DATA, f"E1-exact-{tag.split()[0]}.npz"),
             nu=nu, kind=B["kind"], k=kk, size=ii, n2=a2, nh=ah, imax=im,
             single=np.array([(r[0], r[1], r[2], r[3], r[4]) for r in single]),
             groups=np.array([np.array(g) for g in grp], dtype=object), allow_pickle=True)
    return dict(tag=tag, mp=mp, nu=nu, groups=grp, single=single, sets=sets)


# ================================================================ метод 2


def analyse_coll(tag, a_fun, N_list, N_main):
    say("")
    say("=" * 100)
    say(f"МЕТОД 2 (коллокация) для L_a: {tag}")
    say("=" * 100)
    mp = model_params(a_fun, 1 << 13)
    nu_m, _, _, _ = model_nu(KMAX, mp["l_p"], mp["l_m"])
    store = {}
    for N in N_list:
        t_start = time.time()
        d = build(N, a_fun)
        lam, VL, VR = eigens(d)
        V = duals(VL, VR)
        mu = np.sort(np.abs(np.sqrt(lam[:KMAX])))
        res = max(residual(d, VR[:, j], lam[j]) for j in range(KMAX))
        lead = list(range(min(250, VR.shape[1])))
        bio = np.abs(V[:, lead].conj().T @ VR[:, lead] - np.eye(len(lead))).max()
        store[N] = dict(d=d, lam=lam, VR=VR, V=V, mu=mu, resid=res, bio=bio)
        dev = mu - nu_m
        say(f"  N = {N:4d}: max |sqrt(lam) - nu(T)| = {np.abs(dev).max():.4f}"
            f" (первые 60: {np.abs(dev[:60]).max():.4f}); невязка пар {res:.1e};"
            f" ||V^H Z - I|| (250) {bio:.1e}; время {time.time()-t_start:.1f} c")
    st = store[N_main]
    mu = st["mu"]
    rows = []
    for k in (0, 1, 2, 3, 4, 9, 19, 49, 99, 149, 199):
        rows.append((k + 1, f"{nu_m[k]:9.4f}", f"{mu[k]:9.4f}", f"{mu[k]-nu_m[k]:+.4f}"))
    table(["k", "nu_k (модель T)", "sqrt(lam_k) (коллокация)", "разность"], rows)
    mg, _ = cluster(mu, EPS_GROUP)
    say(f"  группировка sqrt(lam) при N = {N_main}: групп {len(mg)}")
    single = []
    for i, g in enumerate(mg):
        idx = [j for j in g]
        n2, nh = proj_norms(st["d"], st["VR"], st["V"], idx)
        single.append((i + 1, len(g), float(mu[g[0]]), n2, nh))
    say(f"  ||P_s||_L2: min {min(r[3] for r in single):.6f},"
        f" медиана {np.median([r[3] for r in single]):.6f},"
        f" max {max(r[3] for r in single):.6f}")
    say(f"  ||P_s||_H01: min {min(r[4] for r in single):.3f},"
        f" медиана {np.median([r[4] for r in single]):.3f},"
        f" max {max(r[4] for r in single):.3f}")
    ws = sorted(single, key=lambda r: -r[3])
    table(["группа", "размер", "sqrt(lam)", "||P_s||_L2", "||P_s||_H01"],
          [(r[0], r[1], f"{r[2]:8.3f}", f"{r[3]:.6f}", f"{r[4]:9.3f}") for r in ws[:5]])
    say("  чувствительность к разрешению (нарастающие наборы):")
    rows = []
    for m in (10, 40, 100, 196):
        row = [m]
        for N in N_list:
            sN = store[N]
            gN, _ = cluster(sN["mu"], EPS_GROUP)
            if m > len(gN):
                row += ["-", "-"]
                continue
            idx = [j for s in range(m) for j in gN[s]]
            n2, nh = proj_norms(sN["d"], sN["VR"], sN["V"], idx)
            row += [f"{n2:.4f}", f"{nh:.1f}"]
        rows.append(tuple(row))
    table(["m"] + [f"N={N}: L2" for N in N_list] + [f"N={N}: H01" for N in N_list], rows)
    np.savez(os.path.join(DATA, f"E1-coll-{tag.split()[0]}.npz"),
             mu=mu, nu_model=nu_m,
             single=np.array([(r[0], r[1], r[2], r[3], r[4]) for r in single]),
             groups=np.array([np.array(g) for g in mg], dtype=object), allow_pickle=True)
    return dict(tag=tag, mp=mp, nu=nu_m, groups=mg, single=single, store=store)


R = []
for tag, af in (("P1 a=1/2+x/4", lambda x: 0.5 + x / 4),
                ("P2 a=1/2+x/3", lambda x: 0.5 + x / 3)):
    e = analyse_exact(tag, af)
    c = analyse_coll(tag, af, N_LIST, N_MAIN)
    R.append((e, c))

# ================================================================ K1


say("")
say("=" * 100)
say("K1. Контроль: a = 1/2 (известный ответ C3) — частоты модели, коллокация, нормы")
say("=" * 100)
a_const = lambda x: np.full_like(x, 0.5)
mp_c = model_params(a_const, 1 << 13)
nu_c, nu_pc, nu_mc, _ = model_nu(KMAX, mp_c["l_p"], mp_c["l_m"])
ex_c = np.sort(np.concatenate([1.5 * np.pi**2 * (np.arange(0, KMAX) + 0.5) ** 2,
                               0.5 * np.pi**2 * (np.arange(0, KMAX) + 1.0) ** 2]))
say(f"  l_+ = {mp_c['l_p']:.9f} (sqrt(2/3) = {math.sqrt(2/3):.9f});"
    f"  l_- = {mp_c['l_m']:.9f} (sqrt(2) = {math.sqrt(2):.9f})")
say(f"  max |nu_k(T) - sqrt(lambda_k(C3))| = {np.abs(nu_c - np.sqrt(ex_c[:KMAX])).max():.3e}")
K1_COLL = {}
for N in (400, 600, 800):
    d = build(N, a_const)
    lam, VL, VR = eigens(d)
    good = np.sort(lam[(lam.real > 1e-6) & (np.abs(lam.imag) < 1e-9)].real)
    mu = np.sqrt(good[:KMAX])
    err = np.abs(mu / np.sqrt(ex_c[:len(mu)]) - 1).max()
    K1_COLL[N] = float(err)
    say(f"  коллокация N = {N}: max отн. ошибка sqrt(lam) против C3 = {err:.3e}")
d = build(N_MAIN, a_const)
lam, VL, VR = eigens(d)
V = duals(VL, VR)
sel = np.where((lam.real > 1e-6) & (np.abs(lam.imag) < 1e-9))[0]
sel = sel[np.argsort(lam[sel].real)]
rows = []
for j in (0, 1, 2, 24, 99, 199):
    n2, nh = proj_norms(d, VR, V, [int(sel[j])])
    rows.append((j + 1, f"{np.abs(lam[sel[j]])**0.5:8.4f}", f"{n2:.6f}",
                 f"{nh:9.3f}", f"{nh/np.abs(lam[sel[j]])**0.5:.3f}"))
table(["j", "sqrt(lam_j)", "||P_j||_L2 (коллокация)", "||P_j||_H01", "H01/sqrt(lam)"], rows)
Bc = exact_basis(a_const, KMAX)
nu_cs = np.sort(Bc["nu"])
wqc, sigc = Bc["xs_w"], Bc["mp"]["sig_p"]
Fc, dFc = Bc["F"], Bc["dF"]
nrc = np.sqrt(np.einsum("ij,j,ij->i", Fc, wqc, Fc))
Fc, dFc = Fc / nrc[:, None], dFc / nrc[:, None]
rows = []
for j in (0, 1, 2, 24, 99, 199):
    n2 = math.sqrt(float(np.sum(wqc / sigc * Fc[j] ** 2)) / float(np.sum(wqc * Fc[j] ** 2)))
    nh = math.sqrt(float(np.sum(wqc * dFc[j] ** 2)) / float(np.sum(wqc * Fc[j] ** 2)))
    rows.append((j + 1, f"{nu_cs[j]:8.4f}", f"{n2:.6f}", f"{nh:9.3f}", f"{nh/nu_cs[j]:.3f}"))
table(["j", "nu_j", "||P_j||_L2 (метод 1)", "||P_j||_H01", "H01/nu"], rows)
say("  ожидание для a = 1/2: ||P_j||_L2 = 1 (проектор на одну собственную функцию),"
    " ||P_j||_H01 = sqrt(lambda_j) = nu_j")

# ================================================================ сводка

say("")
say("=" * 100)
say("СВОДКА")
say("=" * 100)
say(f"  K0: систематика дискретной H01-полунормы метода 2 — см. таблицу (при m = 200 нужен"
    f" N >= 800).")
say(f"  K1 (a = 1/2): max |nu(T) - sqrt(lambda(C3))| = {np.abs(nu_c - np.sqrt(ex_c[:KMAX])).max():.1e};"
    f" коллокация N = 400/600/800: "
    + ", ".join(f"{K1_COLL[N]:.1e}" for N in (400, 600, 800)))
say(f"  K2: |l(M=8192) - l(quad)| <= "
    f"{max(abs(v['simpson'][1][0]-v['quad'][0]) for v in K2.values()):.1e} по l_+ и"
    f" {max(abs(v['simpson'][1][1]-v['quad'][1]) for v in K2.values()):.1e} по l_-")
say(f"  K3: невязки модели (A) до {max(res_k3):.1e}")
say(f"  K4: разность первых sqrt(lambda) модели T и коллокации N = 1600: см. таблицу выше")
for e, c in R:
    a2 = np.array([s["n2"] for s in e["sets"]])
    ah = np.array([s["nh"] for s in e["sets"]])
    ii = np.array([s["size"] for s in e["sets"]])
    kk = np.array([s["k"] for s in e["sets"]])
    im = np.array([s["imax"] for s in e["sets"]])
    say(f"  {e['tag']}: метод 1 — групп {len(e['groups'])};"
        f" ||P_s||_L2 в [{min(r[3] for r in e['single']):.6f},"
        f" {max(r[3] for r in e['single']):.6f}]; ||P_s||_H01 в"
        f" [{min(r[4] for r in e['single']):.2f}, {max(r[4] for r in e['single']):.2f}]")
    say(f"     {NSETS} случайных Phi: ||P||_L2 в [{a2.min():.6f}, {a2.max():.6f}]"
        f" (наклоны: {np.polyfit(ii, a2, 1)[0]:+.6f} на функцию,"
        f" {np.polyfit(kk, a2, 1)[0]:+.6f} на группу,"
        f" log-log по nu_max {np.polyfit(np.log(im), np.log(a2), 1)[0]:+.4f})")
    say(f"     ||P||_H01 в [{ah.min():.2f}, {ah.max():.2f}]"
        f" (наклон log-log по nu_max {np.polyfit(np.log(im), np.log(ah), 1)[0]:.4f},"
        f" nu_max до {im.max():.1f})")
    say(f"     метод 2 (коллокация N = {N_MAIN}): ||P_s||_L2 в"
        f" [{min(r[3] for r in c['single']):.4f}, {max(r[3] for r in c['single']):.4f}],"
        f" ||P_s||_H01 до {max(r[4] for r in c['single']):.1f}, групп {len(c['groups'])}")
say(f"  полное время расчёта {time.time() - T0:.1f} c")

summary = dict(seed=SEED, eps=EPS_GROUP, kmax=KMAX, nsets=NSETS, n_list=list(N_LIST),
               n_main=N_MAIN, m_grid=M_GRID,
               k1=dict(model_dev=float(np.abs(nu_c - np.sqrt(ex_c[:KMAX])).max()),
                       coll_rel={str(k): v for k, v in K1_COLL.items()}),
               k2={k: dict(l_p=v["simpson"][1][0], l_m=v["simpson"][1][1],
                           quad_p=v["quad"][0], quad_m=v["quad"][1], exact=v["exact"])
                   for k, v in K2.items()},
               k3_resid_max=float(max(res_k3)))
for e, c in R:
    key = "p1" if "P1" in e["tag"] else "p2"
    a2 = np.array([s["n2"] for s in e["sets"]])
    ah = np.array([s["nh"] for s in e["sets"]])
    ii = np.array([s["size"] for s in e["sets"]])
    kk = np.array([s["k"] for s in e["sets"]])
    im = np.array([s["imax"] for s in e["sets"]])
    summary[key] = dict(
        l_p=e["mp"]["l_p"], l_m=e["mp"]["l_m"], n_groups=len(e["groups"]),
        single_l2_min=float(min(r[3] for r in e["single"])),
        single_l2_max=float(max(r[3] for r in e["single"])),
        single_h1_min=float(min(r[4] for r in e["single"])),
        single_h1_max=float(max(r[4] for r in e["single"])),
        random_l2_min=float(a2.min()), random_l2_max=float(a2.max()),
        random_h1_min=float(ah.min()), random_h1_max=float(ah.max()),
        slope_l2_per_value=float(np.polyfit(ii, a2, 1)[0]),
        slope_l2_per_group=float(np.polyfit(kk, a2, 1)[0]),
        slope_l2_loglog=float(np.polyfit(np.log(im), np.log(a2), 1)[0]),
        slope_h1_loglog=float(np.polyfit(np.log(im), np.log(ah), 1)[0]),
        coll_single_l2_min=float(min(r[3] for r in c["single"])),
        coll_single_l2_max=float(max(r[3] for r in c["single"])),
        coll_single_h1_max=float(max(r[4] for r in c["single"])),
        coll_groups=len(c["groups"]),
        coll_dev_max=float(np.abs(c["store"][N_MAIN]["mu"] - c["nu"]).max()),
        coll_bio=float(c["store"][N_MAIN]["bio"]))
summary["seconds"] = float(time.time() - T0)
with open(os.path.join(DATA, "summary.json"), "w", encoding="utf-8") as fh:
    json.dump(summary, fh, ensure_ascii=False, indent=1)
with open(os.path.join(DATA, "run.log"), "w", encoding="utf-8") as fh:
    fh.write("\n".join(LOG) + "\n")
say(f"  данные: {DATA}")
