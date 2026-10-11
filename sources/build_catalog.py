"""Проверка скачанных полных текстов и обновление локального реестра."""
from pathlib import Path
import hashlib, json
import fitz

ARXIV = [
 ('S1','2107.12209','Natalia P. Bondarenko','Inverse spectral problems for functional-differential operators with involution','Редукция к матричной задаче; обратная задача, не теорема о нашей базисности.'),
 ('S4','0906.2631','Christian Wyss','Riesz Bases for p-Subordinate Perturbations of Normal Operators','Основной абстрактный инструмент для скобок после симметризации.'),
 ('S7','1401.2574','Anton A. Lunyov; Mark M. Malamud','On the completeness and Riesz basis property of root subspaces of boundary value problems for first order systems and applications','Полнота и базис подпространств для систем; преобразование нашей задачи требует отдельной проверки.'),
 ('S8','1504.04954','Anton A. Lunyov; Mark M. Malamud','On the Riesz basis property of root vectors system for 2 × 2 Dirac type operators','Регулярность и строгая регулярность; условия относятся к системе первого порядка.'),
 ('S9','2012.11170','Anton A. Lunyov; Mark M. Malamud','Stability of spectral characteristics and Bari basis property of boundary value problems for 2 × 2 Dirac type systems','Устойчивость спектральных данных; различие базисов Бари и Рисса.'),
 ('S10','1109.3683','Mark M. Malamud; Leonid L. Oridoroga','On the completeness of the system of root vectors for first-order systems','Слабая регулярность краевых условий как механизм полноты.'),
 ('S11','1608.00224','Boris Mityagin; Petr Siegl','Local form-subordination condition and Riesz basisness of root systems','Локальная подчинённость и спектральные зазоры; возможный более сильный инструмент.'),
 ('S12','2411.10553','Boris Mityagin; Petr Siegl','Local form subordination without a power decay and a criterion of Riesz basesness','Развитие локальной подчинённости; не переносится автоматически на старшую производную.'),
 ('S13','1106.5774','Plamen Djakov; Boris Mityagin','Criteria for existence of Riesz bases consisting of root functions of Hill and 1D Dirac operators','Критерии перехода от двумерных спектральных блоков к отдельным функциям.'),
 ('S14','1108.4225','Plamen Djakov; Boris Mityagin','Riesz bases consisting of root functions of 1D Dirac operators','Критерии обычного базиса внутри спектральных блоков.'),
 ('S15','1403.2973','Plamen Djakov; Boris Mityagin','Riesz basis property of Hill operators with potentials in weighted spaces','Сравнительный материал о спектральных зазорах и обусловленности; другой оператор.'),
 ('S16','1108.0344','Plamen Djakov; Boris Mityagin','Equiconvergence of spectral decompositions of 1D Dirac operators with regular boundary conditions','Регулярность, строгая регулярность и сходимость спектральных разложений.'),
 ('S17','0901.0856','Plamen Djakov; Boris Mityagin','Bari-Markus property for Riesz projections of 1D periodic Dirac operators','Контроль разностей проекторов; механизм базиса подпространств.'),
 ('S18','0803.3170','Plamen Djakov; Boris Mityagin','Bari-Markus property for Riesz projections of Hill operators with singular potentials','Контроль спектральных проекторов второго порядка.'),
 ('S19','0808.3447','Hans Zwart','Riesz basis for strongly continuous groups','Полнота, зазоры и группы операторов; одна отделённость спектра без остальных условий недостаточна.'),
 ('S20','1202.5204','A. A. Shkalikov','Eigenvalue Asymptotics of Perturbed Self-adjoint Operators','Счётная функция и локальная подчинённость; вспомогательный контекст для кластеризации.'),
 ('S21','0811.2337','A. A. Shkalikov; O. A. Veliev','On the Riesz Basis Property of the Eigen- and Associated Functions of Periodic and Antiperiodic Sturm-Liouville Problems','Сравнение обычного базиса и базиса со скобками; иной тип краевых условий.'),
]
OTHER = [
 ('S3','Shkalikov-rm9740','А. А. Шкаликов','Возмущения самосопряженных и нормальных операторов с дискретным спектром','Успехи матем. наук 71:5(431) (2016), 113–174','https://doi.org/10.4213/rm9740','https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9740&what=fullt&option_lang=rus','Обзор теории подчинённых возмущений; теорема 6.6 уточняет теорему Маркуса–Мацаева и служит второй опорой C6. PDF и распознанный LaTeX-исходник взяты из локального архива пользователя: загрузка с MathNet не удалась.'),
 ('S2','Kopzhassarova-2012','Asylzat Kopzhassarova; Abdizhakhan Sarsenbi','Basis Properties of Eigenfunctions of Second-Order Differential Operators with Involution','2012, Article 576843','https://doi.org/10.1155/2012/576843','https://pdfs.semanticscholar.org/0990/6f9700628fdffdaf59f16f6e86c1b01b8789.pdf','Явные постоянные модели с отражением; не переменный коэффициент.'),
 ('S5','Polyakov-Bari','Dmitry M. Polyakov','On the Bari basis property for even-order differential operators with involution','Tamkang J. Math. 54(4), 339–351 (2023); online 2022','https://doi.org/10.5556/j.tkjm.54.2023.4899','https://journals.math.tku.edu.tw/index.php/TKJM/article/download/4899/1711/11817','Базисность для отражения старшей производной; порядок строго больше двух, другие условия.'),
 ('S6','Sarsenbi-2021','Abdissalam Sarsenbi; Abdizhahan Sarsenbi','On Eigenfunctions of the Boundary Value Problems for Second Order Differential Equations with Involution','Symmetry 13(10), 1972 (2021)','https://doi.org/10.3390/sym13101972','https://pdfs.semanticscholar.org/564a/51b028faf6adfad6b2c5aff627db4efe825c.pdf','Постоянная главная часть, функции Грина и равносходимость; условия Дирихле проекта не подменяются.'),
]
rows=[]
for code,aid,authors,title,role in ARXIV:
 filename = 'Wyss-0906.2631v1.pdf' if code=='S4' else aid+'v1.pdf'
 rows.append(dict(code=code,authors=authors,title=title,version='arXiv:'+aid+'v1',url='https://arxiv.org/abs/'+aid+'v1',pdf_url='https://arxiv.org/pdf/'+aid+'v1',filename=filename,role=role))
for code,name,authors,title,version,url,pdf,role in OTHER:
 rows.append(dict(code=code,authors=authors,title=title,version=version,url=url,pdf_url=pdf,filename=name+'.pdf',role=role))
rows.sort(key=lambda x:int(x['code'][1:]))
for r in rows:
 p=Path('output/literature')/r['filename']
 assert p.read_bytes().startswith(b'%PDF-'), p
 with fitz.open(p) as doc:
  assert len(doc)>1
  r['pages']=len(doc)
  texts=[page.get_text() for page in doc]
  assert sum(map(len,texts))>1000
  p.with_suffix('.txt').write_text('\f'.join(texts),encoding='utf-8')
 r['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 r['status']='PDF получен, текст извлечён; проверенные теоремы — в results.md.'
Path('sources/papers.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
out=['# Подборка полных текстов','', 'Дата: 10.10.2026. В подборке 21 статья; книги, лекция и черновик в счёт не входят. PDF и извлечённый текст лежат в `output/literature/`, вне Git. Наличие полного текста не означает проверку его теорем.','', 'Работы о других операторах включены ради методов: полнота, подчинённость, спектральные проекторы. Для переменного $a$ ни одна из них не даёт готовой теоремы. Карточки использованных результатов — в [results.md](results.md).','']
for r in rows:
 out += [f"## {r['code']}. {r['title']}",'',f"**Авторы:** {r['authors']}. **Версия:** {r['version']}.",f"[Первичный источник]({r['url']}); [полный текст]({r['pdf_url']}); [локальный PDF](../output/literature/{r['filename']}).",f"**Объём:** {r['pages']} стр. **Статус:** {r['status']}",f"**Связь с проектом:** {r['role']}",f"**SHA-256:** `{r['sha256']}`.",'']
Path('sources/catalog.md').write_text('\n'.join(out),encoding='utf-8')
print(f'Проверено {len(rows)} полных PDF; реестр sources/catalog.md и papers.json обновлён.')
