# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "scipy>=1.11"]
# ///
"""E7 (узел I36, случай (B)): L_a y = -y''(x) - a(x) y''(-x) на (-1,1),
условия y(1)=c y(-1), y'(1)=c y'(-1) (c=+1 периодические, c=-1 антипериодические) или Дирихле.

Метод 1: коллокация Чебышёва-Лобатто; граничные значения y(+-1) исключены через два краевых
условия (отображение E: u -> y), оператор M = (L E) на внутренних узлах; ортонормирование
в дискретном L2 (веса Кленшоу-Кёртиса) через Холецкий G = E^H W E. Собственные пары: scipy.linalg.eig
(правые z_j, левые v_j), двойственный базис V^H Z = I, проектор группы P_I = Z_I V_I^H.
Метод 2 (независимый): конечные разности 2-го порядка на равномерной сетке, неизвестные
(y_0..y_{M-1}, s), s = y'(-1), призрачные узлы y_{-1}=y_1-2hs, y_{M+1}=y_{M-1}+2hcs; обобщённая
задача A u = lambda B u; сравнение первых собственных значений с экстраполяцией Ричардсона.
Случайных чисел нет. Запуск: uv run experiments/E7/run.py [префиксы случаев A0 A1 B B' C C' D]
"""
import time, os, sys
import numpy as np
import scipy.linalg as la

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
os.makedirs(DATA, exist_ok=True)
NS = (400, 600, 800)       # разрешения коллокации
NU_MAX = 100.0             # верхняя граница sqrt(lambda) в анализе
WS = (1.0, 2.0, 4.0)       # длины окон по sqrt(lambda)
DELTAS = (0.05, 0.25)      # пороги цепочечной группировки
FD_M = (400, 800, 1600)
BINS = [(0, 25), (25, 50), (50, 75), (75, 100)]
LOG = []


def say(*p):
    s = " ".join(str(x) for x in p)
    print(s, flush=True)
    LOG.append(s)


def cheb(N):
    k = np.arange(N + 1)
    t = np.cos(np.pi * k / N)
    c = np.ones(N + 1); c[0] = 2; c[-1] = 2
    c = c * (-1.0) ** k
    X = np.tile(t, (N + 1, 1)).T
    dX = X - X.T
    D = np.outer(c, 1 / c) / (dX + np.eye(N + 1))
    D = D - np.diag(D.sum(axis=1))
    return D, t


def clenshaw_curtis(N):
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


def coll(N, a_fun, bc):
    """Матрица Mt в L2_w-ортонормированных координатах. bc in {'per','anti','dir'}."""
    D, t = cheb(N)
    D2 = D @ D
    w = clenshaw_curtis(N)
    Cm = np.zeros((2, N + 1))
    if bc == "dir":
        Cm[0, 0] = 1; Cm[1, N] = 1
    else:
        c = 1.0 if bc == "per" else -1.0
        Cm[0, 0] = 1; Cm[0, N] -= c            # t[0]=+1, t[N]=-1: y(1) - c y(-1)
        Cm[1, :] = D[0, :] - c * D[N, :]       # y'(1) - c y'(-1)
    Cb = Cm[:, [0, N]]
    Ci = Cm[:, 1:N]
    H = -np.linalg.solve(Cb, Ci)
    E = np.zeros((N + 1, N - 1))
    E[1:N, :] = np.eye(N - 1)
    E[0, :] = H[0]; E[N, :] = H[1]
    R = np.eye(N + 1)[::-1]
    Lfull = -(D2 + np.diag(a_fun(t)) @ R @ D2)
    M = (Lfull @ E)[1:N, :]
    G = E.T @ (w[:, None] * E)
    Lc = np.linalg.cholesky(G)
    Mt = Lc.T @ M @ la.solve_triangular(Lc.T, np.eye(N - 1), lower=False)
    return Mt


def spectrum(Mt):
    lam, VL, VR = la.eig(Mt, left=True, right=True)
    nu = np.sqrt(lam.astype(complex))
    order = np.lexsort((nu.imag, np.round(nu.real, 7)))   # пары лямбда, лямбда* различаем по Im
    lam, VL, VR, nu = lam[order], VL[:, order], VR[:, order], nu[order]
    VR = VR / np.linalg.norm(VR, axis=0)
    VL = VL / np.linalg.norm(VL, axis=0)
    s = np.einsum("ij,ij->j", VL.conj(), VR)
    V = VL / s.conj()[None, :]        # V_j^H z_j = 1
    return lam, nu, VR, V, 1.0 / np.abs(s)


def group_stats(Z, V, idx):
    Zi = Z[:, idx]; Vi = V[:, idx]
    sv = la.svdvals(Zi)
    cond_gram = (sv[0] / sv[-1]) ** 2
    _, Rz = np.linalg.qr(Zi); _, Rv = np.linalg.qr(Vi)
    pn = la.svdvals(Rz @ Rv.conj().T)[0]
    return cond_gram, pn


def windows(nu, W, numax):
    """Границы окон: номинально jW, сдвинуты в наибольший зазор sqrt(lambda) в пределах +-W/4."""
    re = nu.real
    gaps = re[1:] - re[:-1]
    mids = 0.5 * (re[1:] + re[:-1])
    cuts = [-1]
    j = 1
    while j * W + W / 4 <= numax:
        m = np.where((mids >= j * W - W / 4) & (mids <= j * W + W / 4) & (np.arange(len(mids)) > cuts[-1]) & (gaps > 1e-6))[0]
        if len(m):
            cuts.append(int(m[np.argmax(gaps[m])]))
        j += 1
    return [np.arange(cuts[i] + 1, cuts[i + 1] + 1) for i in range(len(cuts) - 1)]


def chains(nu, delta, numax):
    re = nu.real
    n = int(np.searchsorted(re, numax))
    groups, cur = [], [0]
    for i in range(1, n):
        if re[i] - re[i - 1] < delta:
            cur.append(i)
        else:
            groups.append(np.array(cur)); cur = [i]
    return groups  # оборванная по NU_MAX последняя группа не берётся


def exact_a_half(bc, kmax=200):
    if bc == "per":
        out = [0.0] + [1.5 * np.pi**2 * k**2 for k in range(1, kmax)] + [0.5 * np.pi**2 * k**2 for k in range(1, kmax)]
    elif bc == "anti":
        out = [1.5 * np.pi**2 * (k + .5)**2 for k in range(kmax)] + [0.5 * np.pi**2 * (k + .5)**2 for k in range(kmax)]
    else:
        out = [1.5 * np.pi**2 * (k + .5)**2 for k in range(kmax)] + [0.5 * np.pi**2 * (k + 1)**2 for k in range(kmax)]
    return np.sort(np.array(out))


CASES = [
    ("A0 a=1/2, per", lambda x: 0.5 + 0 * x, "per"),
    ("A1 a=1/2, anti", lambda x: 0.5 + 0 * x, "anti"),
    ("B a=1/2+x/4, per [a(1)!=a(-1)]", lambda x: 0.5 + x / 4, "per"),
    ("B' a=1/2+x/4, anti [a(1)!=a(-1)]", lambda x: 0.5 + x / 4, "anti"),
    ("C a=1/2+x^2/4, per [a(1)=a(-1)]", lambda x: 0.5 + x**2 / 4, "per"),
    ("C' a=1/2+x^2/4, anti [a(1)=a(-1)]", lambda x: 0.5 + x**2 / 4, "anti"),
    ("D a=1/2+x/4, Dirichlet", lambda x: 0.5 + x / 4, "dir"),
]


def binline(rows):
    s = []
    for lo, hi in BINS:
        m = (rows[:, 0] >= lo) & (rows[:, 0] < hi)
        if m.sum():
            s.append(f"[{lo},{hi}): n={int(m.sum())} размер<={int(rows[m,1].max())} cond<={rows[m,2].max():.3g} ||P||<={rows[m,3].max():.3g}")
    return "; ".join(s)


def analyse(name, afun, bc):
    say(f"\n===== {name} =====")
    res = {}
    for N in NS:
        t1 = time.time()
        Mt = coll(N, afun, bc)
        lam, nu, Z, V, kap = spectrum(Mt)
        resid = np.linalg.norm(Mt @ Z - Z * lam[None, :], axis=0) / (np.abs(lam) + 1.0)
        biorth = np.abs(V.conj().T @ Z - np.eye(len(lam))).max()
        res[N] = dict(lam=lam, nu=nu, Z=Z, V=V, kap=kap)
        n = int(np.searchsorted(nu.real, NU_MAX))
        say(f" N={N}: {time.time()-t1:.1f} c; собств. значений {len(lam)}, с Re sqrt<={NU_MAX}: {n}; "
            f"max|Im lam|/|lam| {np.max(np.abs(lam[:n].imag)/(np.abs(lam[:n])+1e-12)):.2e}; "
            f"max невязка {resid[:n].max():.2e}; max|V^H Z-I| {biorth:.2e}")
    n_ref = int(np.searchsorted(res[NS[-1]]["nu"].real, NU_MAX))
    for a, b in zip(NS[:-1], NS[1:]):
        k = min(int(np.searchsorted(res[a]["nu"].real, NU_MAX)), int(np.searchsorted(res[b]["nu"].real, NU_MAX)))
        d = np.abs(res[a]["lam"][:k] - res[b]["lam"][:k]) / (np.abs(res[b]["lam"][:k]) + 1.0)
        say(f" разность собств. значений N={a} vs {b}: max {d.max():.2e} по {k} знач., в первых 30: {d[:30].max():.2e}")
    if np.allclose(afun(np.array([0.3, -0.3])), 0.5):
        ex = exact_a_half(bc)
        lam = res[NS[-1]]["lam"][:n_ref]
        err = np.abs(np.sort(lam.real) - ex[:n_ref]) / (ex[:n_ref] + 1.0)
        say(f" КОНТРОЛЬ точный спектр a=1/2: max отн. ошибка по {n_ref} знач. {err.max():.2e}; max|Im| {np.abs(lam.imag).max():.1e}")
    for N in NS:
        n = int(np.searchsorted(res[N]["nu"].real, NU_MAX))
        kap = res[N]["kap"][:n]; nuu = res[N]["nu"].real[:n]
        parts = [f"[{lo},{hi}): {kap[(nuu>=lo)&(nuu<hi)].max():.3g}" for lo, hi in BINS if ((nuu >= lo) & (nuu < hi)).any()]
        say(f" N={N}: нормы одиночных проекторов 1/|v^H z|, max по интервалам sqrt: " + "; ".join(parts))
    out = {}
    for W in WS:
        say(f" -- окна длины W={W} (границы в наибольшем зазоре, +-W/4)")
        for N in NS:
            r = res[N]
            rows = []
            for g in windows(r["nu"], W, NU_MAX):
                cg, pn = group_stats(r["Z"], r["V"], g)
                rows.append((r["nu"].real[g].mean(), len(g), cg, pn, r["nu"].real[g[0]], r["nu"].real[g[-1]]))
            rows = np.array(rows)
            out[(W, N)] = rows
            say(f"   N={N}: " + binline(rows))
        a_, b_ = out[(W, NS[-2])], out[(W, NS[-1])]
        kk = min(len(a_), len(b_))
        d = np.abs(a_[:kk, 3] - b_[:kk, 3]) / b_[:kk, 3]
        dc = np.abs(a_[:kk, 2] - b_[:kk, 2]) / b_[:kk, 2]
        say(f"   разность N={NS[-2]} vs {NS[-1]} по {kk} окнам: ||P|| max отн. {d.max():.2e}, cond max отн. {dc.max():.2e}; "
            f"размеры окон совпадают: {bool((a_[:kk,1]==b_[:kk,1]).all())}")
        rr = out[(W, NS[-1])]
        np.savetxt(os.path.join(DATA, f"windows_{name.split()[0].replace(chr(39),'p')}_W{W}_N{NS[-1]}.csv"), rr,
                   header="nu_mean size cond_gram proj_norm nu_min nu_max", delimiter=",")
        m = rr[:, 0] > 10
        if m.sum() > 3:
            sl = np.polyfit(np.log(rr[m, 0]), np.log(rr[m, 3]), 1)[0]
            sl2 = np.polyfit(np.log(rr[m, 0]), np.log(rr[m, 2]), 1)[0]
            say(f"   наклон log||P||/log nu (nu>10): {sl:+.2f}; наклон log cond/log nu: {sl2:+.2f}")
    r = res[NS[-1]]
    if name.split()[0] in ("B", "B'"):
        say(" первые 14 собств. значений (N=%d): lambda, Im sqrt, kappa=1/|v^H z|" % NS[-1])
        for j in range(14):
            say(f"   {j:2d} {r['lam'][j].real:+.8f}{r['lam'][j].imag:+.3e}j  nu={r['nu'][j].real:.6f}{r['nu'][j].imag:+.2e}j  kappa={r['kap'][j]:.3f}")
    rr = out[(2.0, NS[-1])]
    wk = int(np.argmax(rr[:, 2]))
    g = windows(r["nu"], 2.0, NU_MAX)[wk]
    say(f" окно W=2 с наибольшей cond: nu in [{rr[wk,4]:.4f},{rr[wk,5]:.4f}], размер {len(g)}, cond {rr[wk,2]:.3g}, ||P|| {rr[wk,3]:.3g}")
    for j in g:
        say(f"     nu={r['nu'][j].real:.6f}{r['nu'][j].imag:+.3e}j kappa={r['kap'][j]:.3g}")
    # нормы частичных сумм спектральных проекторов S_i = P_{0..i} (разрез после i-го по Re sqrt)
    nn = int(np.searchsorted(r["nu"].real, NU_MAX))
    Zr, Vr = r["Z"], r["V"]
    sn = np.full(nn - 1, np.nan)
    for i in range(nn - 1):
        if r["nu"].real[i + 1] - r["nu"].real[i] > 1e-6:
            _, Rz = np.linalg.qr(Zr[:, :i + 1]); _, Rv = np.linalg.qr(Vr[:, :i + 1])
            sn[i] = la.svdvals(Rz @ Rv.conj().T)[0]
    cutnu = r["nu"].real[:nn - 1]
    ok = ~np.isnan(sn)
    parts = []
    for lo, hi in BINS:
        m = ok & (cutnu >= lo) & (cutnu < hi)
        if m.sum():
            parts.append(f"[{lo},{hi}): разрезов {int(m.sum())}, min {sn[m].min():.3g}, медиана {np.median(sn[m]):.3g}, max {sn[m].max():.3g}")
    say(" нормы частичных сумм S_i (разрез после i по возрастанию Re sqrt): " + "; ".join(parts))
    for W in (2.0, 4.0):
        best = []
        for j in range(int(NU_MAX // W)):
            m = ok & (cutnu >= j * W) & (cutnu < (j + 1) * W)
            if m.sum():
                best.append((j * W, sn[m].min()))
        best = np.array(best)
        parts = []
        for lo, hi in BINS:
            mm = (best[:, 0] >= lo) & (best[:, 0] < hi)
            if mm.sum():
                parts.append(f"[{lo},{hi}): {best[mm,1].max():.3g}")
        say(f" лучший разрез в каждом отрезке длины {W}: max по отрезкам из min ||S_i||: " + "; ".join(parts))
    # самое плохое окно W=2
    wk2 = int(np.argmax(out[(2.0, NS[-1])][:, 3]))
    g2 = windows(r["nu"], 2.0, NU_MAX)[wk2]
    lo_i, hi_i = g2[0], g2[-1]
    say(f" окно W=2 с наибольшей ||P||: nu in [{r['nu'].real[lo_i]:.4f},{r['nu'].real[hi_i]:.4f}], размер {len(g2)}, ||P|| {out[(2.0,NS[-1])][wk2,3]:.3g}; "
        f"зазоры до соседей снаружи: слева {r['nu'].real[lo_i]-r['nu'].real[lo_i-1]:.3g}, справа {r['nu'].real[hi_i+1]-r['nu'].real[hi_i]:.3g}; "
        f"kappa соседей: {r['kap'][lo_i-1]:.3g}, {r['kap'][hi_i+1]:.3g}")
    # пары соседних собственных значений: расстояние d=|nu_{j+1}-nu_j| и обусловленность пары
    n = int(np.searchsorted(r["nu"].real, NU_MAX)) - 1
    prs = []
    for j in range(n - 1):
        d = abs(r["nu"][j + 1] - r["nu"][j])
        if d < 0.5:
            cg, pn = group_stats(r["Z"], r["V"], np.array([j, j + 1]))
            prs.append((r["nu"][j].real, d, cg, pn, abs(r["nu"][j].imag) + abs(r["nu"][j + 1].imag)))
    prs = np.array(prs)
    if len(prs) > 4:
        o = np.argsort(prs[:, 1])[:6]
        say(f" пары соседних с d<0.5: {len(prs)} шт; 6 ближайших (nu, d, cond пары, ||P|| пары):")
        for q in o:
            say(f"     nu={prs[q,0]:.3f} d={prs[q,1]:.3e} cond={prs[q,2]:.4g} ||P||={prs[q,3]:.4g}")
        m = prs[:, 1] > 1e-4
        if m.sum() > 4:
            sl = np.polyfit(np.log(prs[m, 1]), np.log(prs[m, 2]), 1)[0]
            say(f"     наклон log cond / log d по парам: {sl:+.2f}; max cond пары {prs[:,2].max():.4g}")
    for dl in DELTAS:
        r = res[NS[-1]]
        rows = []
        for g in chains(r["nu"], dl, NU_MAX):
            cg, pn = group_stats(r["Z"], r["V"], g)
            rows.append((r["nu"].real[g].mean(), len(g), cg, pn))
        say(f" -- цепочки, порог {dl} (N={NS[-1]}): " + binline(np.array(rows)))
    r = res[NS[-1]]
    s = []
    for K in (10, 20, 40, 60):
        if K <= n_ref:
            sv = la.svdvals(r["Z"][:, :K])
            s.append(f"K={K}: {(sv[0]/sv[-1])**2:.3g}")
    say(" накопленная cond Грама первых K норм. собств. функций: " + "; ".join(s))
    return res


def fd_eigs(M, afun, c):
    h = 2.0 / M
    x = -1 + h * np.arange(M + 1)
    n = M + 1
    Pm = np.zeros((n, n))
    for j in range(M):
        Pm[j, j] = 1
    Pm[M, 0] = c
    D2 = np.zeros((n, n))
    for j in range(1, M):
        D2[j, :] = (Pm[j + 1] - 2 * Pm[j] + Pm[j - 1]) / h**2
    sc = np.zeros(n); sc[M] = 1.0
    D2[0, :] = (2 * Pm[1] - 2 * Pm[0] - 2 * h * sc) / h**2
    D2[M, :] = (2 * Pm[M - 1] - 2 * Pm[M] + 2 * h * c * sc) / h**2
    A = -(D2 + np.diag(afun(x)) @ D2[::-1, :])
    lam = la.eig(A, Pm, right=False)
    lam = lam[np.isfinite(lam)]
    nu = np.sqrt(lam.astype(complex))
    return lam[np.lexsort((nu.imag, np.round(nu.real, 7)))]


def fd_check(name, afun, c, k=12):
    say(f"\n--- независимый метод (конечные разности), {name}: первые {k} собств. значений ---")
    L = {}
    for M in FD_M:
        t1 = time.time()
        L[M] = fd_eigs(M, afun, c)[:k]
        say(f"   M={M}: {time.time()-t1:.1f} c")
    d1 = L[FD_M[1]] - L[FD_M[0]]
    d2 = L[FD_M[2]] - L[FD_M[1]]
    p = np.log2(np.abs(d1) / np.abs(d2))
    rich = L[FD_M[2]] + d2 / (2 ** np.median(p.real) - 1)
    lc = la.eigvals(coll(NS[-1], afun, "per" if c == 1 else "anti"))
    nuc = np.sqrt(lc.astype(complex))
    lc = lc[np.lexsort((nuc.imag, np.round(nuc.real, 7)))][:k]
    say(f"   j   lambda_coll(N={NS[-1]})   lambda_FD(M={FD_M[2]})   Richardson   |coll-Rich|   p_obs")
    for j in range(k):
        say(f"   {j:2d}  {lc[j]:.10f}  {L[FD_M[2]][j]:.8f}  {rich[j]:.8f}  {abs(lc[j]-rich[j]):.2e}  {p[j].real:.2f}")


if __name__ == "__main__":
    which = sys.argv[1:]
    if "LARGE" in which:
        which.remove("LARGE")
        NS = (1000, 1300, 1600)
        NU_MAX = 250.0
        BINS = [(0, 50), (50, 100), (100, 150), (150, 200), (200, 250)]
        LARGE = True
    else:
        LARGE = False
    for name, af, bc in CASES:
        if which and name.split()[0] not in which:
            continue
        analyse(name, af, bc)
    if (not which and not LARGE) or "FD" in which:
        fd_check("a=1/2+x/4, per", lambda x: 0.5 + x / 4, 1.0)
        fd_check("a=1/2+x/4, anti", lambda x: 0.5 + x / 4, -1.0)
    say(f"\nполное время {time.time()-T0:.0f} c")
    if LARGE or not which:
        with open(os.path.join(HERE, "run_large.log" if LARGE else "run.log"), "w", encoding="utf-8") as f:
            f.write("\n".join(LOG))
