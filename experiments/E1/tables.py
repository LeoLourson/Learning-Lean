# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26"]
# ///
"""E1: пересборка главных таблиц из сохранённых данных data/*.npz и data/summary.json.

Запуск: uv run experiments/E1/tables.py
Печатает те числа, которые приведены в README.md (проверка, что README не разошёлся с данными).
"""
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

with open(os.path.join(DATA, "summary.json"), encoding="utf-8") as fh:
    S = json.load(fh)

print("summary.json: seed =", S["seed"], " eps =", S["eps"], " kmax =", S["kmax"],
      " nsets =", S["nsets"], " N =", S["n_list"], " M =", S["m_grid"])
for k in ("k1", "k3_resid_max"):
    print(f"  {k}: {S[k]}")

for tag in ("P1", "P2"):
    z = np.load(os.path.join(DATA, f"E1-exact-{tag}.npz"), allow_pickle=True)
    g = z["groups"]
    sizes = {}
    for gr in g:
        sizes[len(gr)] = sizes.get(len(gr), 0) + 1
    print(f"\n=== метод 1, {tag} (данные data/E1-exact-{tag}.npz) ===")
    print(f"  функций {len(z['nu'])}, групп {len(g)}, размеры {dict(sorted(sizes.items()))}")
    print(f"  nu: {z['nu'][0]:.4f} .. {z['nu'][-1]:.4f}")
    n2, nh = z["n2"], z["nh"]
    im = z["imax"]
    print(f"  ||P_Phi||_L2 : min {n2.min():.6f} max {n2.max():.6f} медиана {np.median(n2):.6f}")
    print(f"  ||P_Phi||_H01: min {nh.min():.2f} max {nh.max():.2f} медиана {np.median(nh):.2f}")
    print(f"  наклон L2 (log-log по nu_max): {np.polyfit(np.log(im), np.log(n2), 1)[0]:+.4f}")
    print(f"  наклон H01 (log-log по nu_max): {np.polyfit(np.log(im), np.log(nh), 1)[0]:.4f}")
    # нормы одиночных групп
    sing = np.array([(r[3], r[4], r[2]) for r in z["single"]])
    print(f"  по группам: ||P_s||_L2 min {sing[:,0].min():.6f} max {sing[:,0].max():.6f};"
          f" ||P_s||_H01 min {sing[:,1].min():.2f} max {sing[:,1].max():.2f}")
    print(f"  ||P_s||_H01 / nu_max(s): min {np.min(sing[:,1]/sing[:,2]):.3f},"
          f" max {np.max(sing[:,1]/sing[:,2]):.3f}")
    c = np.load(os.path.join(DATA, f"E1-coll-{tag}.npz"), allow_pickle=True)
    sc = np.array([(r[3], r[4]) for r in c["single"]])
    print(f"  метод 2 (коллокация N={S['n_main']}): групп {len(c['groups'])},"
          f" ||P_s||_L2 в [{sc[:,0].min():.4f}, {sc[:,0].max():.4f}],"
          f" ||P_s||_H01 до {sc[:,1].max():.1f}")
    print(f"  метод 2: max |sqrt(lam) - nu(T)| = {S[tag.lower()]['coll_dev_max']:.4f},"
          f" ||V^H Z - I|| = {S[tag.lower()]['coll_bio']:.1e}")
print(f"\nполное время расчёта: {S['seconds']:.1f} c")
