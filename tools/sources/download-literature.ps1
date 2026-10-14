$ErrorActionPreference = 'Stop'
# tools/sources -> корень проекта на два уровня выше
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
# Восстанавливает LaTeX-исходники и PDF, перечисленные в sources/registry.json, и сверяет контрольные суммы.
& python (Join-Path $projectRoot 'tools/sources/lit.py') fetch
if ($LASTEXITCODE -ne 0) { throw 'Часть полных текстов не восстановлена: смотри строки с пометкой ОШИБКА выше.' }
