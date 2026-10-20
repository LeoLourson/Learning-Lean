# Работа математика с проектом

Команды, роли и файлы, куда каждая из них пишет. Порядок шагов задают `.claude/commands/`,
права ролей — `.claude/agents/`, пути классов — `LAYOUT.md`; при расхождении со схемой
первичны они.

## Ежедневный цикл `/day`

```mermaid
flowchart TD
    U([Математик: /day + пожелание]) --> S1

    subgraph S1["1. Состояние"]
        direction TB
        G["git status, git log"] --> CH["build_index.py --check<br/>structure.py"]
        CH --> RD["question.md, blueprint.md,<br/>идеи I*"]
    end

    S1 --> S2

    subgraph S2["2. Идеи (/ideas)"]
        direction TB
        IG["idea-generator<br/>→ новый I*"] --> CR["critic<br/>→ «Критика» в I*"]
        CR --> VD{"вердикт"}
        VD -- "смертельное возражение" --> REJ["I*: rejected,<br/>причина остаётся"]
        VD -- "выдержала" --> EXP["experimenter<br/>→ experiments/E*"]
    end

    S2 --> S3{"3. Цель дня"}
    S3 -- "C* own-result, проверена,<br/>без Lean" --> FORM
    S3 -- "C* без проверки" --> REF
    S3 -- "идея выдержала критику" --> PROOF
    S3 -- "замечания проверок" --> SRC

    PROOF["Доказательство:<br/>новый C*, идея → promoted"] --> REF

    subgraph REF["/referee"]
        direction TB
        RR["referee<br/>→ «Рецензия» в C*"] --> RV{"вердикт"}
        RV -- "пробел" --> FIX["исправить C*"] --> RR
    end
    RV -- "принято" --> FORM

    subgraph FORM["/formalize"]
        direction TB
        FM["formalizer<br/>→ Involution/&lt;Слой&gt;"] --> LB["lake build,<br/>#print axioms"]
        LB --> FC["fidelity-checker<br/>→ «Соответствие» в C*"]
        FC --> LT["шапка C*: lean_theorem"]
    end

    subgraph SRC["/sources"]
        direction TB
        LS["literature-scout<br/>→ отчёт"] --> ADD["lit.py add<br/>→ registry.json"]
        ADD --> TR["/transcribe<br/>latex-transcriber"]
        TR --> CARD["карточка S*"] --> SV["source-verifier<br/>→ «Сверка» в S*"]
    end

    FORM --> S5
    SRC --> S5
    S3 -- "цели нет" --> S6

    S5["5. Заготовка Aristotle<br/>tasks/A*/package, один sorry"] -. "отправка только<br/>по прямой просьбе" .-> AR[(Aristotle)]
    AR -. "answer/ → перенос,<br/>lake build, report.md" .-> FORM

    S5 --> S6["6. Завершение:<br/>build_index, gen_status,<br/>check.ps1, harness check"]
    S6 --> S7([7. Отчёт: доказано, вердикты,<br/>открытые узлы, решения за пользователем])
    S7 -. "результат меняет ответ" .-> EXPO["/exposition<br/>→ paper/exposition.tex"]
    S7 -. "коммит" .-> U
```

## Откуда берутся сводки

Состояние единицы хранится только в шапке её файла; остальное собирают инструменты.

```mermaid
flowchart LR
    subgraph P["Первичное (пишет человек и роли)"]
        C["C* записи"]
        I["I* идеи"]
        S["S* карточки"]
        Q["question.md"]
        L["Involution/**"]
        R["registry.json"]
    end

    subgraph D["Производное (не править руками)"]
        IX["index.md"]
        BP["blueprint.md"]
        ST["paper/generated/status.tex"]
        AX["output/generated/Axioms.lean"]
        CT["sources/catalog.md"]
    end

    C & I & S --> BI["build_index.py"] --> IX & BP
    C --> GS["gen_status.py"] --> ST
    C -- "final: true" --> GL["gen_ledger.py"] --> AX
    L --> GL
    R --> LIT["lit.py catalog"] --> CT
    ST --> REV["paper/review.tex"]
```

## Кто кого проверяет

Роль не проверяет свою работу; проверяющий получает текст без рассуждений автора.

```mermaid
flowchart LR
    IG[idea-generator] -- "I*" --> CR[critic]
    AUTH[автор записи] -- "C*" --> RF[referee]
    FM[formalizer] -- "Lean" --> FC[fidelity-checker]
    LT[latex-transcriber] -- "транскрипция" --> CARD[карточка S*] --> SV[source-verifier]
    MS[mathlib-scout] -. "имена" .-> FM
    LS[literature-scout] -. "кандидаты" .-> SEL[отбор основной моделью]
```
