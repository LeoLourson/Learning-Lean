# A8: отчёт о переносе

- Куда перенесено: модуль `SobolevClosure` (в текущем дереве
  `Involution/Estimates/SobolevClosure.lean`). Объявления:
  `Involution.memIntervalH01_iff_trace`, `Involution.memDirichletH2_iff_h2_and_h01`;
  определения `IsTestPair`, `MemIntervalH01` приняты 11.10.2026. Запись `C` у узла
  S-DOMAIN нет: утверждение живёт в разделе «Область определения» постановки `Q`.
- Правки после переноса: перенесён один изменённый файл из 99 отправленных; правок
  формулировок нет.
- Сверено: заголовки двух теорем и определения совпадают с заготовкой; `sorry` и
  `axiom` отсутствуют; модуль собран локально с закреплёнными версиями; аудит аксиом
  отмечен в `blueprint.md`, выписка — в ответе сервиса.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-domain-result.tar.gz`.
