#!/usr/bin/env python3
"""Сборка фрагмента `paper/generated/status.tex` из шапок единиц.

Формат взят из заготовки, оставленной вершиной `paper`: окружение `center`,
`\\renewcommand{\\arraystretch}{1.2}` и `tabular` из трёх столбцов
(`Запись`, `Статус`, `Объявление Lean`) с вертикальными линейками. Фрагмент
включается статьёй командой `\\input{generated/status.tex}` и не несёт ни
подписи, ни метки. Статус печатается каноническим ключом FACETS.md: заголовки
записей в таблицу не входят, поэтому она остаётся узкой.

Режим `--check` ничего не пишет: печатает расхождение и возвращает 1, если
файл устарел. Даты в файл не попадают, иначе проверка свежести невозможна.
"""

from __future__ import annotations

import argparse
import difflib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import facets as F  # noqa: E402

BANNER = "% generated; do not edit"
REL = "paper/generated/status.tex"
# Классы, чьи статусы попадают в таблицу: заготовка вершины paper читает
# шапки claims/C*.md — записи результата, а не артефакты процесса.
TABLE_CLASSES = ("record",)


def latex_escape(value: str) -> str:
    """Экранирует символы, ломающие tabular, не трогая формулы `$...$`.

    Заголовок считается LaTeX-фрагментом: обратная косая черта, фигурные
    скобки и `$` передаются как есть; вне формул экранируются `_ % & # ~ ^`,
    внутри формул — только `% & #`.
    """
    out: list[str] = []
    in_math = False
    for ch in value:
        if ch == "$":
            in_math = not in_math
            out.append(ch)
            continue
        if in_math:
            out.append("\\" + ch if ch in "%&#" else ch)
            continue
        if ch in "_%&#":
            out.append("\\" + ch)
        elif ch == "~":
            out.append("\\textasciitilde{}")
        elif ch == "^":
            out.append("\\textasciicircum{}")
        elif ch in "\r\n":
            out.append(" ")
        else:
            out.append(ch)
    return "".join(out).strip()


def latex_breakable(name: str) -> str:
    """Имя объявления с разрешёнными переносами.

    Полные имена вида `Involution.tiltedCoefficient_bracket_basis` не переносятся
    и дают Overfull в таблице; `\\allowbreak` после точки и подчёркивания это снимает.
    """
    escaped = latex_escape(name)
    escaped = escaped.replace("\\_", "\\_\\allowbreak ")
    return escaped.replace(".", ".\\allowbreak ")


def render(data: dict) -> str:
    units = [u for u in data["units"] if u.cls in TABLE_CLASSES and u.status()]
    lines = [
        BANNER,
        "% Источник: шапки claims/C*.md (id, status, lean_theorem). Пересобирает tools/state/gen_status.py.",
        "% Статус — канонический ключ FACETS.md: unverified-source, own-result, goal, proved-lean, proved-aristotle.",
        "% Строк: {n}.".format(n=len(units)),
        "\\begin{center}",
        "\\small",
        "\\renewcommand{\\arraystretch}{1.2}",
        "\\begin{tabular}{|l|l|l|}",
        "\\hline",
        "\\textbf{Запись} & \\textbf{Статус} & \\textbf{Объявление Lean}\\\\\\hline",
    ]
    for unit in units:
        lean = unit.facets.get("lean_theorem")
        lines.append(
            "{id} & {status} & {lean}\\\\\\hline".format(
                id=latex_escape(unit.id),
                status=latex_escape(unit.status()),
                lean=("\\texttt{" + latex_breakable(str(lean)) + "}") if lean else "---",
            )
        )
    if not units:
        lines.append("% В claims/ нет записей с фасетом status.")
    lines += ["\\end{tabular}", "\\end{center}", ""]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description="Сборка paper/generated/status.tex.")
    parser.add_argument("--root", default=str(Path(__file__).resolve().parents[2]), help="корень проекта")
    parser.add_argument("--check", action="store_true", help="не писать, только сообщить об устаревшем файле")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    units, _naming = F.load_units(root)
    data = {"units": sorted(units, key=lambda unit: F.id_sort_key(unit.id))}
    fresh = render(data)
    path = root / REL

    try:
        current = path.read_text(encoding="utf-8") if path.is_file() else None
    except (OSError, UnicodeDecodeError) as exc:
        print(f"устарел: {REL} — не прочитан ({exc})", file=sys.stderr)
        return 1

    if current == fresh:
        print(f"без изменений: {REL}")
        return 0
    if args.check:
        print(f"устарел: {REL}" + ("" if current is not None else " (файла нет)"))
        if current is not None:
            diff = difflib.unified_diff(
                current.split("\n"), fresh.split("\n"), fromfile=REL, tofile=REL + " (заново)", lineterm=""
            )
            for i, line in enumerate(diff):
                if i >= 20:
                    print("  ...")
                    break
                print("  " + line)
        print("запусти `python tools/state/gen_status.py`.")
        return 1
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(fresh, encoding="utf-8", newline="\n")
    print(f"записан: {REL}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
