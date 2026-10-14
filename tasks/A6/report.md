# A6: отчёт о переносе

- Куда перенесено: модуль `NearlyEvenBrackets` (в текущем дереве
  `Involution/Estimates/NearlyEvenBrackets.lean`). Объявления:
  `Involution.nearlyEven_gauge_data`, `Involution.nearlyEven_bracket_basis`,
  `Involution.nearlyEven_bracket_rootVectors`.
- Правки после переноса: добавлен импорт `BracketCorollaries`, следствие
  `nearlyEven_bracket_rootVectors` и перенесена одна строка; формулировки не менялись.
- Сверено: изменился только `Involution/Estimates/NearlyEvenBrackets.lean`; формулировка леммы с `sorry`
  и итоговой теоремы совпадает с заготовкой; `sorry`, `admit`, `axiom` отсутствуют;
  модуль собран локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-nearly-even-result.tar.gz`.
