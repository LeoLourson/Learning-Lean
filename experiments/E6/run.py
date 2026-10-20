# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E6 (узел I35): L_a^Theta напрямую против оператора формы-суммы T_b K_Theta.

L_a y = -y''(x) - a(x) y''(-x) на (-1,1), условия Y' + Theta Y = 0, Theta = h*I:
  y'(1) + h y(1) = 0,  -y'(-1) + h y(-1) = 0   (h = 0: Нейман, h = 1: Штурм).

Метод D1: коллокация Чебышёва-Лобатто (граничные строки -- условия), обобщённая задача A y = lam B y.
Метод D2: конечные разности второго порядка с фиктивными узлами (условия исключают их).
Метод F : Галёркин на форме идеи I35, базис -- ортонормированные полиномы Лежандра степени <= N в H^1
  без краевых условий:  A_ij = int (r phi_j)'(w phi_i)' dx + h * sum_{x=+-1} phi_j phi_i   (rw = 1),
  G_ij = <T_b^{-1} phi_j, phi_i>, T_b^{-1} = (1 - b^2)^{-1}(I - bR) (b чётна),  A c = lam G c.
  Для контроля A собирается и в раскрытом виде t0 + b-форма (шаг 4 идеи): разность A.

Случаи:
  const : a = 1/2 (r = 1, b = 1/2): точный спектр (1+a)k^2, k tan k = h (чётные),
          (1-a)k^2, k cot k = -h... (нечётные: h sin k + k cos k = 0).
          Нейман: k = pi n; k = pi(n - 1/2).
  lin   : a = 1/2 + x/4. q = a/Ra = (2+x)/(2-x), rho = q^2, r = q^(1/4), r'/r = 1/(4-x^2),
          b = a/r^2 = sqrt(4-x^2)/4 (чётна).
  kink  : b = 0.4, q = exp(g), g(x) = 0.8*clip(x,-0.8,0.8) (нечётная), r = q^(1/4), a = b q^(1/2);
          r' разрывна при |x| = 0.8 и ненулевая при |x|<0.8 (r'(+-1) = 0): излом q.
"""
import time
import numpy as np
import scipy.linalg as sla
from numpy.polynomial import legendre as L

NEIG = 40
t_start = time.time()


# ---------------------------------------------------------------- коэффициенты
def make_case(name):
    if name == "const":
        a = lambda x: 0.5 + 0 * x
        r = lambda x: 1 + 0 * x
        rp = lambda x: 0 * x
        b = lambda x: 0.5 + 0 * x
        br = [-1, 1]
    elif name == "lin":
        a = lambda x: 0.5 + x / 4
        r = lambda x: ((2 + x) / (2 - x)) ** 0.25
        rp = lambda x: r(x) / (4 - x**2)
        b = lambda x: np.sqrt(4 - x**2) / 4
        br = [-1, 1]
    elif name == "kink":
        g = lambda x: 0.8 * np.clip(x, -0.8, 0.8)
        a = lambda x: 0.4 * np.exp(g(x) / 2)
        r = lambda x: np.exp(g(x) / 4)
        rp = lambda x: r(x) * 0.2 * (np.abs(x) < 0.8)
        b = lambda x: 0.4 + 0 * x
        br = [-1, -0.8, 0.8, 1]
    return dict(a=a, r=r, rp=rp, b=b, br=br)


# ---------------------------------------------------------------- прямая: Чебышёв
def cheb(N):
    x = np.cos(np.pi * np.arange(N + 1) / N)
    c = np.hstack([2, np.ones(N - 1), 2]) * (-1) ** np.arange(N + 1)
    X = np.tile(x, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D -= np.diag(D.sum(axis=1))
    return D, x


def direct_cheb(case, h, N):
    D, x = cheb(N)
    D2 = D @ D
    F = np.fliplr(np.eye(N + 1))  # x_j -> x_{N-j} = -x_j
    A = -D2 - np.diag(case["a"](x)) @ F @ D2
    B = np.eye(N + 1)
    A[0, :] = D[0, :]
    A[0, 0] += h
    B[0, :] = 0
    A[N, :] = -D[N, :]
    A[N, N] += h
    B[N, :] = 0
    w = sla.eig(A, B, right=False)
    w = w[np.isfinite(w) & (np.abs(w) < 1e5)]
    w = w[np.argsort(w.real)]
    return w[:NEIG]


# ---------------------------------------------------------------- прямая: FD
def direct_fd(case, h, n):
    hh = 2.0 / n
    x = -1 + hh * np.arange(n + 1)
    D2 = np.zeros((n + 1, n + 1))
    for i in range(1, n):
        D2[i, i - 1] = D2[i, i + 1] = 1
        D2[i, i] = -2
    D2[0, 1] = 2
    D2[0, 0] = -(2 + 2 * hh * h)
    D2[n, n - 1] = 2
    D2[n, n] = -(2 + 2 * hh * h)
    D2 /= hh**2
    F = np.fliplr(np.eye(n + 1))
    A = -D2 - np.diag(case["a"](x)) @ F @ D2
    w = sla.eigvals(A)
    w = w[np.argsort(w.real)]
    return w[:NEIG]


# ---------------------------------------------------------------- форма: Галёркин
def legendre_basis(N, x):
    """phi_k, phi_k' в точках x: (N+1, len(x))."""
    V = L.legvander(x, N)  # (m, N+1)
    nrm = np.sqrt((2 * np.arange(N + 1) + 1) / 2)
    P = V * nrm
    dP = np.zeros_like(P)
    for k in range(N + 1):
        e = np.zeros(N + 1)
        e[k] = 1
        dP[:, k] = L.legval(x, L.legder(e)) * nrm[k]
    return P.T, dP.T


def quad_nodes(br, npts):
    xg, wg = L.leggauss(npts)
    xs, ws = [], []
    for lo, hi in zip(br[:-1], br[1:]):
        xs.append((hi - lo) / 2 * xg + (hi + lo) / 2)
        ws.append((hi - lo) / 2 * wg)
    return np.concatenate(xs), np.concatenate(ws)


def form_matrices(case, h, N):
    npts = N + 40
    x, wq = quad_nodes(case["br"], npts)
    P, dP = legendre_basis(N, x)
    r, rp, b = case["r"](x), case["rp"](x), case["b"](x)
    w_, wp = 1 / r, -rp / r**2
    # (r phi_j)' (w phi_i)' : A_ij = sum_q wq * u_j' stuff
    Ru = rp * P + r * dP  # (r phi)'
    Wv = wp * P + w_ * dP  # (w phi)'
    A = (Wv * wq) @ Ru.T  # A[i,j]
    # раскрытый вид: t0 + b-форма:  int phi_j' phi_i' + w r' phi_j phi_i' + r w' phi_j' phi_i + r' w' phi_j phi_i
    A2 = (dP * wq) @ dP.T
    A2 += (dP * wq) @ (P * (w_ * rp)).T  # i-й: phi_i' ; j-й: w r' phi_j
    A2 += (P * wq) @ (dP * (r * wp)).T  # i-й: phi_i ; j-й: r w' phi_j'
    A2 += (P * wq) @ (P * (rp * wp)).T
    # граничный член: h * r(+-1) w(+-1) phi_j phi_i = h phi_j phi_i
    xb = np.array([1.0, -1.0])
    Pb, _ = legendre_basis(N, xb)
    Bd = h * (Pb @ Pb.T)
    A = A + Bd
    A2 = A2 + Bd
    # G_ij = <T_b^{-1} phi_j, phi_i> = int (phi_j - b phi_j(-x)) phi_i /(1-b^2)
    Pm, _ = legendre_basis(N, -x)  # phi_j(-x)
    G = (P * (wq / (1 - b**2))) @ (P - b * Pm).T  # [i,j]
    G = (G + G.T) / 2
    # Gram для y = r u:  int r^2 phi phi
    Gy = (P * (wq * r**2)) @ P.T
    return A, A2, G, Gy


def form_eig(case, h, N, want_vec=False):
    A, A2, G, Gy = form_matrices(case, h, N)
    diff = np.abs(A - A2).max() / np.abs(A).max()
    if not want_vec:
        w = sla.eig(A, G, right=False)
        w = w[np.argsort(w.real)]
        return w[:NEIG], diff
    w, C = sla.eig(A, G)
    idx = np.argsort(w.real)
    return w[idx], C[:, idx], diff, G, Gy, A


# ---------------------------------------------------------------- точный спектр a = 1/2
def exact_const(h, n):
    out = []
    for kind in ("e", "o"):
        ks = []
        m = 1
        while len(ks) < n:
            if kind == "e":
                f = lambda k: h * np.cos(k) - k * np.sin(k)  # y'(1)+h y(1), y=cos kx
                lo = (m - 1) * np.pi
            else:
                f = lambda k: h * np.sin(k) + k * np.cos(k)  # y=sin kx
                lo = (m - 1) * np.pi
            # корни f на (lo, lo+pi]; ищем сканом
            kk = np.linspace(lo + 1e-9, lo + np.pi, 4001)
            v = np.array([f(t) for t in kk])
            for i in range(len(kk) - 1):
                if v[i] == 0 or v[i] * v[i + 1] < 0:
                    from scipy.optimize import brentq
                    ks.append(brentq(f, kk[i], kk[i + 1], xtol=1e-14))
            m += 1
        ks = np.array(sorted(ks))
        ks = ks[ks > 1e-9] if not (kind == "e" and h == 0) else ks
        out.append(ks[:n])
    ke, ko = out
    # Нейман: чётная серия k = pi n, n>=0 (k=0 даёт lam = 0)
    lam = np.concatenate([1.5 * ke**2, 0.5 * ko**2])
    return np.sort(lam)[:NEIG]


def exact_const_neumann(n):
    ke = np.pi * np.arange(0, n)
    ko = np.pi * (np.arange(1, n + 1) - 0.5)
    return np.sort(np.concatenate([1.5 * ke**2, 0.5 * ko**2]))[:NEIG]


def exact(h):
    if h == 0:
        return exact_const_neumann(60)
    return exact_const(h, 60)


# ---------------------------------------------------------------- отчёт
def fmt_row(lbl, vals):
    return lbl + " " + " ".join(f"{v:10.5f}" for v in vals)


def maxdiff(u, v, rel=True):
    d = np.abs(u - v)
    if rel:
        d = d / np.maximum(np.abs(v), 1)
    return d.max()


def run_case(name, h):
    case = make_case(name)
    print(f"\n=== случай {name}, h = {h} ===")
    t0 = time.time()
    res = {}
    Ncheb = [60, 100, 140]
    Nform = [60, 100, 140]
    nfd = [400, 800, 1600]
    for N in Ncheb:
        res[("cheb", N)] = direct_cheb(case, h, N)
    for N in Nform:
        w, diff = form_eig(case, h, N)
        res[("form", N)] = w
        print(f"  форма N={N}: max|A_свёрн - A_раскр|/max|A| = {diff:.2e}")
    for n in nfd:
        res[("fd", n)] = direct_fd(case, h, n)
    # Richardson для FD
    f1, f2 = res[("fd", 800)].real, res[("fd", 1600)].real
    res[("fdR", 0)] = f2 + (f2 - f1) / 3
    print(f"  время методов {time.time()-t0:.1f} c")
    # сходимость (по первым NEIG; относительно max(|v|,1))
    print("  Разности между разрешениями (max_j |dl_j|/max(|l_j|,1), первые 40, Re):")
    for m in ("cheb", "form"):
        Ns = Ncheb if m == "cheb" else Nform
        for i in range(len(Ns) - 1):
            d = maxdiff(res[(m, Ns[i])].real, res[(m, Ns[i + 1])].real)
            print(f"    {m:5s} N={Ns[i]}->{Ns[i+1]}: {d:.2e}")
    for i in range(len(nfd) - 1):
        d = maxdiff(res[("fd", nfd[i])].real, res[("fd", nfd[i + 1])].real)
        print(f"    fd    n={nfd[i]}->{nfd[i+1]}: {d:.2e}")
    for m, key in (("cheb", ("cheb", Ncheb[-1])), ("form", ("form", Nform[-1]))):
        print(f"  max|Im lam| {m}: {np.abs(res[key].imag).max():.2e}")
    # сравнение методов
    ref_c = res[("cheb", Ncheb[-1])].real
    ref_f = res[("form", Nform[-1])].real
    print("  Сравнение (макс. относительная разность по первым 40):")
    print(f"    форма(140) vs cheb(140): {maxdiff(ref_f, ref_c):.2e}")
    print(f"    форма(140) vs fd Richardson: {maxdiff(ref_f, res[('fdR',0)]):.2e}")
    print(f"    cheb(140) vs fd Richardson : {maxdiff(ref_c, res[('fdR',0)]):.2e}")
    print(f"    fd 1600 vs fd Richardson   : {maxdiff(res[('fd',1600)].real, res[('fdR',0)]):.2e}")
    if name == "const":
        ex = exact(h)
        print(f"    точный vs форма(140): {maxdiff(ref_f, ex):.2e};  точный vs cheb(140): {maxdiff(ref_c, ex):.2e}"
              f";  точный vs fd(1600): {maxdiff(res[('fd',1600)].real, ex):.2e}")
    print("   j    cheb140      form140      fdRich       |form-cheb|")
    for j in range(NEIG):
        if j < 12 or j % 4 == 3:
            print(f"  {j+1:2d} {ref_c[j]:12.6f} {ref_f[j]:12.6f} {res[('fdR',0)][j]:12.6f} {abs(ref_f[j]-ref_c[j]):10.2e}")
    return res


def window_norms(name, h, N=140, K=60):
    case = make_case(name)
    w, C, diff, G, Gy, A = form_eig(case, h, N, want_vec=True)
    Cinv = np.linalg.inv(C)
    sel = np.arange(K)
    Cs, Rs = C[:, sel], Cinv[sel, :]
    biorth = np.abs(Rs @ Cs - np.eye(K)).max()
    resid = np.linalg.norm(A @ Cs - G @ Cs * w[sel], axis=0) / np.linalg.norm(G @ Cs, axis=0)
    Ly = np.linalg.cholesky(Gy).T  # Gy = Ly^T Ly
    Lyi = np.linalg.inv(Ly)
    Pj = [Cs[:, [j]] @ Rs[[j], :] for j in range(K)]
    # префиксные суммы по окнам: используем кумулятивные суммы проекторов
    S = np.concatenate([np.zeros((1,) + Pj[0].shape), np.cumsum(np.array(Pj), axis=0)])
    # проекторы на все смежные окна (i..j) в y-L2: ||Ly P Ly^{-1}||_2
    best = {}
    singles = [np.linalg.norm(Ly @ Pj[j] @ Lyi, 2) for j in range(K)]
    for lim in (10, 20, 40, 60):
        m = 0
        for i in range(lim):
            for j in range(i + 1, lim + 1):
                P = S[j] - S[i]
                m = max(m, np.linalg.norm(Ly @ P @ Lyi, 2))
        best[lim] = m
    print(f"\n--- нормы проекторов, {name}, h={h}, Галёркин N={N}, K={K} первых значений ---")
    print(f"  cond(C[:,:K]) = {np.linalg.cond(Cs):.2e}; biorth err = {biorth:.2e}; макс. невязка собств. пар = {resid.max():.2e}")
    print(f"  max Im lam (первые {K}) = {np.abs(w[:K].imag).max():.2e}")
    print("  одиночные ||P_j|| в L2(y): min={:.3f} med={:.3f} max={:.3f}; j=1,10,20,40,60: {}".format(
        min(singles), np.median(singles), max(singles),
        " ".join(f"{singles[j-1]:.3f}" for j in (1, 10, 20, 40, 60))))
    print("  max ||P_window|| по всем смежным окнам внутри первых lim значений:")
    print("   " + "  ".join(f"lim={l}: {best[l]:.3f}" for l in best))
    return best


if __name__ == "__main__":
    np.set_printoptions(linewidth=200)
    for name, h in (("const", 0.0), ("const", 1.0), ("lin", 0.0), ("lin", 1.0), ("kink", 1.0)):
        run_case(name, h)
    print("\n\n######## нормы проекторов Рисса по смежным окнам ########")
    for name, h in (("const", 1.0), ("lin", 0.0), ("lin", 1.0)):
        window_norms(name, h, N=140, K=60)
        window_norms(name, h, N=180, K=60)
    print(f"\nВсего {time.time()-t_start:.1f} c")
