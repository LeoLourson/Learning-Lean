#!/usr/bin/env python3
"""Инварианты раскладки новой папки проекта.

Проверяет по пунктам и возвращает 1 при нарушениях:

1. соразмерность: каждый отслеживаемый файл (кроме `.git`, `.lake`, `output`,
   `.dsh`, `__pycache__`) попадает ровно в один класс из `LAYOUT.md`;
2. шапки: обязательные фасеты из `FACETS.md`, `id` = префикс имени файла,
   уникальность идентификаторов, допустимые статусы, `lean_theorem` там, где
   он обязателен;
3. ссылки: `depends_on`/`applies_to`/`goal` разрешаются, `depends_on`
   ацикличен, в `claims/` нет ссылок вида «файл:строка»;
4. производное: у `index.md`, `blueprint.md`, `sources/catalog.md`,
   `paper/generated/status.tex` есть баннер `generated`, и файлы совпадают с
   тем, что дают генераторы (байт в байт);
5. Lean: заголовок `module` у каждого модуля `Involution/**`, достижимость из
   `Involution.lean`, отсутствие импортов несуществующих модулей, модуль слоя
   *k* не импортирует слой выше *k*;
6. следы шаблона в `.claude/commands/**`, `.claude/agents/**`.

Проверка рассчитана на неполное состояние: отсутствие файла перечисляется как
нарушение, а не как падение.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "state"))
import build_index  # noqa: E402
import facets as F  # noqa: E402
import gen_status  # noqa: E402

FILE_LINE_RE = re.compile(r"(?<![\w/])([\w./+-]+\.(?:md|lean|tex|py|ps1|json|toml|yml|yaml)):(\d+)")
CHECKED_BY_RE = re.compile(r"^[a-z][a-z-]* \d{4}-\d{2}-\d{2}$")
TEMPLATE_DIRS = (".claude/commands", ".claude/agents")
TEMPLATE_TRACES = ("proj.py", "PROJECT.md", "paper/main.tex", "mcp__proj", "results/R", "cards/S")
GROUP_THRESHOLD = 8


class Report:
    def __init__(self) -> None:
        self.violations: list[str] = []

    def section(self, title: str) -> None:
        print("")
        print(f"== {title} ==")

    def ok(self, message: str) -> None:
        print(f"  [ok] {message}")

    def note(self, message: str) -> None:
        print(f"  [i] {message}")

    def bad(self, message: str) -> None:
        print(f"  [!] {message}")
        self.violations.append(message)


def grouped(paths: list[str], threshold: int = GROUP_THRESHOLD) -> list[str]:
    """Неклассифицированные пути: короткие группы поимённо, длинные — счётом."""
    groups: dict[str, list[str]] = {}
    for path in paths:
        top = path.split("/")[0] if "/" in path else path
        groups.setdefault(top, []).append(path)
    lines: list[str] = []
    for top in sorted(groups):
        items = groups[top]
        if len(items) > threshold:
            sample = ", ".join(items[:3])
            lines.append(f"{top}: {len(items)} файлов, например {sample}, ...")
        else:
            lines.extend(items)
    return lines


def read_text(path: Path):
    try:
        return path.read_text(encoding="utf-8"), ""
    except OSError as exc:
        return None, f"не прочитан: {exc}"
    except UnicodeDecodeError as exc:
        return None, f"не UTF-8: {exc}"


# --------------------------------------------------------------------------


def check_layout(root: Path, report: Report, rules: list[F.ClassRule]) -> None:
    report.section("1. Классификация файлов")
    if not rules:
        report.bad("LAYOUT.md: таблица классов не прочитана")
        return
    files = F.tracked_files(root)
    counts: dict[str, int] = {}
    unclassified: list[str] = []
    ambiguous: list[tuple[str, list[str]]] = []
    for rel in files:
        matches = F.classify(rel, rules)
        if not matches:
            unclassified.append(rel)
        elif len(matches) > 1:
            ambiguous.append((rel, [m.name for m in matches]))
        else:
            name = matches[0].name
            counts[name] = counts.get(name, 0) + 1
    report.ok(f"отслеживаемых файлов: {len(files)}; классов в LAYOUT.md: {len(rules)}")
    print("  классы: " + ", ".join(f"{name}={counts[name]}" for name in sorted(counts)))
    if ambiguous:
        for rel, names in ambiguous:
            report.bad(f"{rel}: попадает сразу в классы {', '.join(names)}")
    else:
        report.ok("файлов, попавших в два класса, нет")
    if unclassified:
        report.bad(f"неклассифицированных файлов: {len(unclassified)}")
        for line in grouped(unclassified):
            print(f"      {line}")
    else:
        report.ok("неклассифицированных файлов нет")


def check_facets(root: Path, report: Report, units: list[F.Unit], naming: list[str]) -> dict[str, list[str]]:
    report.section("2. Шапки единиц")
    ids: dict[str, list[str]] = {}
    checks: list[tuple[str, list[str]]] = []
    problems_before = len(report.violations)
    for note in naming:
        report.bad(note)
    for unit in units:
        for error in unit.header_errors:
            report.bad(error)
        if unit.id != unit.id_hint:
            report.bad(f"{unit.rel}: id {unit.id!r} не совпадает с префиксом имени {unit.id_hint!r}")
        for key in F.REQUIRED.get(unit.cls, ()):
            value = unit.facets.get(key)
            if key not in unit.facets or value is None or value == "":
                report.bad(f"{unit.rel}: нет обязательного фасета {key}")
        for key in F.LIST_FACETS:
            value = unit.facets.get(key)
            if value is not None and not isinstance(value, list):
                report.bad(f"{unit.rel}: {key} должен быть списком в квадратных скобках")
        if "final" in unit.facets and not isinstance(unit.facets["final"], bool):
            report.bad(f"{unit.rel}: final должен быть true или false")
        status = unit.status()
        allowed = F.STATUS_ALLOWED.get(unit.cls, ())
        if status and allowed and status not in allowed:
            report.bad(f"{unit.rel}: статус {status!r} вне допустимых {allowed}")
        if status in F.NEEDS_LEAN and not unit.get("lean_theorem"):
            report.bad(f"{unit.rel}: статус {status}, но фасет lean_theorem не заполнен")
        # checked_by — скаляр «роль ГГГГ-ММ-ДД» или список таких проверок
        # (FACETS.md, раздел record); пустой список — ошибка.
        checked = unit.facets.get("checked_by")
        if checked is not None:
            entries = checked if isinstance(checked, list) else [checked]
            if not entries:
                report.bad(f"{unit.rel}: checked_by — пустой список")
            else:
                for entry in entries:
                    if not isinstance(entry, str) or not CHECKED_BY_RE.match(entry):
                        report.bad(f"{unit.rel}: checked_by {entry!r} не вида «роль ГГГГ-ММ-ДД»")
                if all(isinstance(e, str) and CHECKED_BY_RE.match(e) for e in entries):
                    checks.append((unit.id, entries))
        ids.setdefault(unit.id, []).append(unit.rel)
    for unit_id, paths in sorted(ids.items(), key=lambda item: F.id_sort_key(item[0])):
        if len(paths) > 1:
            report.bad(f"идентификатор {unit_id} повторён: {', '.join(paths)}")
    statement = [u for u in units if u.cls == "statement"]
    if not statement:
        report.bad("нет постановки claims/question.md")
    elif len(statement) > 1:
        report.bad(f"постановок несколько: {', '.join(u.rel for u in statement)}")
    total_checks = sum(len(entries) for _unit_id, entries in checks)
    if checks:
        for unit_id, entries in sorted(checks, key=lambda item: F.id_sort_key(item[0])):
            print(f"  [i] {unit_id}: проверок {len(entries)} — {', '.join(entries)}")
    report.note(f"независимых проверок: {total_checks} у {len(checks)} единиц из {len(units)}")
    if len(report.violations) == problems_before:
        report.ok(f"единиц: {len(units)}; обязательные фасеты на месте, идентификаторы уникальны")
    return ids


def check_refs(root: Path, report: Report, units: list[F.Unit], edges: dict[str, list[str]]) -> None:
    report.section("3. Ссылки")
    known = {unit.id for unit in units}
    unresolved: list[str] = []
    for unit in units:
        for key in F.REF_FACETS:
            value = unit.facets.get(key)
            if value is None:
                continue
            refs = value if isinstance(value, list) else [value]
            for ref in refs:
                if str(ref) not in known:
                    unresolved.append(f"{unit.id}.{key} -> {ref}")
    if unresolved:
        for item in sorted(set(unresolved)):
            report.bad(f"не разрешается: {item}")
    else:
        report.ok(f"ссылки depends_on/applies_to/goal/node разрешаются ({len(known)} идентификаторов)")
    cycles = build_index.find_cycles(edges)
    if cycles:
        for cycle in cycles:
            report.bad("цикл depends_on: " + " -> ".join(cycle))
    else:
        report.ok("граф depends_on ацикличен")
    hits: list[str] = []
    claims = root / "claims"
    if claims.is_dir():
        for path in sorted(claims.rglob("*.md")):
            text, error = read_text(path)
            if text is None:
                report.bad(f"{path.relative_to(root).as_posix()}: {error}")
                continue
            for lineno, line in enumerate(text.replace("\r\n", "\n").split("\n"), start=1):
                for match in FILE_LINE_RE.finditer(line):
                    hits.append(f"{path.relative_to(root).as_posix()}:{lineno}: {match.group(0)}")
    if hits:
        for hit in hits:
            report.bad(f"ссылка вида «файл:строка»: {hit}")
    else:
        report.ok("ссылок вида «файл:строка» в claims/ нет")


def check_derived(root: Path, report: Report, data: dict) -> None:
    report.section("4. Производное")
    expectations = {
        "index.md": (F.GENERATED_BANNERS["index"], build_index.render_index(data)),
        "blueprint.md": (F.GENERATED_BANNERS["plan"], build_index.render_blueprint(data)),
        gen_status.REL: (F.GENERATED_BANNERS["statusfrag"], gen_status.render({"units": data["units"]})),
    }
    for rel, (banner, fresh) in expectations.items():
        path = root / rel
        if not path.is_file():
            report.bad(f"{rel}: файла нет")
            continue
        text, error = read_text(path)
        if text is None:
            report.bad(f"{rel}: {error}")
            continue
        first = text.replace("\r\n", "\n").split("\n")[0].strip()
        if first != banner:
            report.bad(f"{rel}: первая строка {first!r}, ожидается баннер {banner!r}")
        else:
            report.ok(f"{rel}: баннер на месте")
        if text != fresh:
            report.bad(f"{rel}: не совпадает с выводом генератора, пересобери")
    catalog = root / "sources" / "catalog.md"
    if not catalog.is_file():
        report.bad("sources/catalog.md: файла нет (собирает tools/sources/lit.py catalog)")
    else:
        text, error = read_text(catalog)
        if text is None:
            report.bad(f"sources/catalog.md: {error}")
        else:
            first = text.replace("\r\n", "\n").split("\n")[0].strip()
            if "generated" in first and "do not edit" in first:
                report.ok("sources/catalog.md: баннер на месте")
            else:
                report.bad(f"sources/catalog.md: первая строка {first!r} без баннера generated")


def check_lean(root: Path, report: Report) -> None:
    report.section("5. Lean: заголовки, достижимость, слои")
    modules = F.lean_modules(root)
    if not (root / "Involution.lean").is_file():
        report.bad("Involution.lean: файла нет")
        return
    modules["Involution"] = "Involution.lean"
    layers = F.layer_order(root)
    imports: dict[str, list[str]] = {}
    header_bad = 0
    checked_headers = 0
    for name in sorted(modules):
        rel = modules[name]
        text, error = read_text(root / rel)
        if text is None:
            report.bad(f"{rel}: {error}")
            continue
        header = F.module_header(text)
        if rel != "Involution.lean":
            checked_headers += 1
            if header != "module":
                header_bad += 1
                report.bad(f"{rel}: первая строка {header!r}, ожидается module")
        elif header != "module":
            report.note(
                f"{rel}: первая строка {header!r}; корневой модуль библиотеки остаётся без заголовка module, "
                "при этом все модули каталога Involution/ его несут"
            )
        imports[name] = F.parse_imports(text)
    if not header_bad:
        report.ok(f"заголовок module у всех {checked_headers} модулей каталога Involution/")
    missing = [
        f"{name} -> {dep}"
        for name, deps in imports.items()
        for dep in deps
        if dep.startswith("Involution") and dep not in modules
    ]
    if missing:
        for item in sorted(set(missing)):
            report.bad(f"импорт несуществующего модуля: {item}")
    else:
        report.ok("импорты Involution.** указывают на существующие модули")
    reachable = {"Involution"}
    frontier = ["Involution"]
    while frontier:
        current = frontier.pop()
        for dep in imports.get(current, []):
            if dep in modules and dep not in reachable:
                reachable.add(dep)
                frontier.append(dep)
    unreachable = sorted(name for name in modules if name not in reachable)
    if unreachable:
        for name in unreachable:
            report.bad(f"{modules[name]}: модуль не достижим из Involution.lean")
    else:
        report.ok(f"все {len(modules)} модулей достижимы из Involution.lean")
    if not layers:
        report.note("порядок слоёв не прочитан из LAYOUT.md — проверка слоёв пропущена")
        return
    layer_bad = 0
    for name in sorted(modules):
        own = F.lean_layer(name, layers)
        if own is None:
            continue
        for dep in imports.get(name, []):
            other = F.lean_layer(dep, layers)
            if other is not None and other > own:
                layer_bad += 1
                report.bad(
                    f"{modules[name]} (слой {layers[own]}) импортирует {modules.get(dep, dep)} (слой {layers[other]})"
                )
    if not layer_bad:
        report.ok(f"модуль слоя k не импортирует слой выше k (слои: {', '.join(layers)})")
    outside = sorted(modules[name] for name in modules if name != "Involution" and F.lean_layer(name, layers) is None)
    if outside:
        report.note(f"вне слоёв: {len(outside)} модулей прямо в Involution/*.lean (переносит агент слоёв)")


def check_template_traces(root: Path, report: Report) -> None:
    report.section("6. Следы шаблона")
    found: list[str] = []
    scanned = 0
    for rel_dir in TEMPLATE_DIRS:
        directory = root / rel_dir
        if not directory.is_dir():
            report.note(f"{rel_dir}: каталога нет")
            continue
        for path in sorted(directory.rglob("*")):
            if not path.is_file():
                continue
            scanned += 1
            text, error = read_text(path)
            rel = path.relative_to(root).as_posix()
            if text is None:
                report.bad(f"{rel}: {error}")
                continue
            for lineno, line in enumerate(text.replace("\r\n", "\n").split("\n"), start=1):
                for trace in TEMPLATE_TRACES:
                    if trace in line:
                        found.append(f"{rel}:{lineno}: {trace}")
    if found:
        for item in found:
            report.bad(f"след шаблона: {item}")
    else:
        report.ok(f"следов шаблона нет (проверено файлов: {scanned})")


def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description="Инварианты раскладки новой папки проекта.")
    parser.add_argument("--root", default=str(Path(__file__).resolve().parents[2]), help="корень проекта")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    report = Report()
    print(f"Проверка раскладки: {root}")

    rules, layout_errors = F.classes_from_layout(root)
    for error in layout_errors:
        report.bad(error)
    units, naming = F.load_units(root)
    data = build_index.collect(root)
    check_layout(root, report, rules)
    check_facets(root, report, units, naming)
    check_refs(root, report, units, data["edges"])
    check_derived(root, report, data)
    check_lean(root, report)
    check_template_traces(root, report)

    print("")
    if report.violations:
        print(f"Нарушений: {len(report.violations)}")
        return 1
    print("Нарушений нет.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
