# A1: что вернул сервис

- Статус: `COMPLETE`, 100 % (`output/aristotle-weak-status.json`, обновлён 09.10.2026
  21:57 по часам сервиса; отправка 10.10.2026).
- Файлы: создан `Involution/WeakConstant.lean`, в `Involution.lean` добавлен импорт
  `import Involution.WeakConstant`.
- `#print axioms Involution.HasWeakDerivOn.ae_eq_const_of_zero` —
  `[propext, Classical.choice, Quot.sound]` (квитанция
  `output/aristotle-weak-regularity-receipt.json`; в сводке сервиса тот же список).
- Версии: проект закреплён на `leanprover/lean4:v4.35.0-rc4`; сервис сообщил
  предпочтительную для него `v4.28.0` (`service_preferred_lean`), доказательство
  перенесено и пересобрано локально в закреплённых версиях.
- Архив: `output/aristotle-weak-result.tar.gz` (распакованного каталога в `output/`
  нет — сохранён только архив).
- Из сводки сервиса: «The statement is exactly the one in `prompt.md`… The file
  contains no `sorry` and adds no axioms… The result is a.e. equality only: there is
  no pointwise statement and no continuity assumption on `f`.»
