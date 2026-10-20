# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=1.26", "matplotlib>=3.8"]
# ///
"""Рисунки к опыту E1: рост норм ||P_Phi||_{L2->L2} и ||P_Phi||_{L2->H01} по данным data/*.npz.

Запуск: uv run experiments/E1/plot.py
Результат: output/experiments/E1-norm-growth.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(ROOT, "output", "experiments")
os.makedirs(OUT, exist_ok=True)

fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
for tag, col, lab in (("P1", "tab:blue", "a = 1/2 + x/4"), ("P2", "tab:red", "a = 1/2 + x/3")):
    f = os.path.join(HERE, "data", f"E1-exact-{tag}.npz")
    if not os.path.exists(f):
        continue
    z = np.load(f, allow_pickle=True)
    im, n2, nh = z["imax"], z["n2"], z["nh"]
    ax[0].plot(im, n2, ".", ms=2.5, color=col, alpha=0.5, label=lab)
    ax[1].plot(im, nh, ".", ms=2.5, color=col, alpha=0.5, label=lab)
    # подгонка log-log
    c2 = np.polyfit(np.log(im), np.log(nh), 1)
    xx = np.linspace(im.min(), im.max(), 20)
    ax[1].plot(xx, np.exp(c2[1]) * xx**c2[0], "-", color=col, lw=1,
               label=f"наклон {c2[0]:.2f}")
ax[0].set_xlabel(r"$\nu_{\max}$ в наборе $\Phi$")
ax[0].set_ylabel(r"$\|\sum_{s\in\Phi}P_s\|_{L_2\to L_2}$")
ax[0].set_title("норма в $L_2$: роста нет")
ax[0].legend(fontsize=8)
ax[0].grid(alpha=0.3)
ax[1].set_xlabel(r"$\nu_{\max}$ в наборе $\Phi$")
ax[1].set_ylabel(r"$\|\sum_{s\in\Phi}P_s\|_{L_2\to H_0^1}$")
ax[1].set_title("норма в $H_0^1$: рост")
ax[1].legend(fontsize=8)
ax[1].grid(alpha=0.3)
fig.suptitle("E1 (узел I22): 500 случайных наборов $\\Phi$, модельный оператор $T$", fontsize=10)
fig.tight_layout()
path = os.path.join(OUT, "E1-norm-growth.png")
fig.savefig(path, dpi=140)
print("saved", path)
