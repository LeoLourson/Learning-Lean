# A1: отчёт о переносе

- Куда перенесено: модуль `WeakConstant` (в исходной раскладке
  `Involution/WeakConstant.lean`, в текущем дереве — `Involution/Setup/WeakConstant.lean`;
  имя модуля перенос не меняет). Объявление:
  `Involution.HasWeakDerivOn.ae_eq_const_of_zero`.
- Импорт модуля зарегистрирован в `Involution.lean`.
- Правки после переноса: не зафиксированы ни в квитанции, ни в `blueprint.md`;
  перенос назван выборочным принятием.
- Сверено: формулировка совпадает с отправленной заготовкой; `sorry`, `admit` и
  `axiom` отсутствуют; модуль собран локально в закреплённых версиях.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — допустимый список.
- Архив: `output/aristotle-weak-result.tar.gz`.
