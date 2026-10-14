# Снимок проекта для внешнего исполнителя: output/snapshot. Ничего не отправляет.
# Снимок производный и не накопитель: целевой каталог чистится перед сборкой.
# Запуск из корня проекта:
#   powershell -NoProfile -ExecutionPolicy Bypass -File tools/host/prepare-input.ps1
$ErrorActionPreference = 'Stop'
# tools/host -> корень проекта на два уровня выше
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$snapshot = Join-Path $projectRoot 'output/snapshot'
$utf8 = [System.Text.UTF8Encoding]::new($false)
$copied = [System.Collections.Generic.List[string]]::new()
$missing = [System.Collections.Generic.List[string]]::new()

function Copy-Record {
    param([string]$Relative)
    if ($copied.Contains($Relative)) { return }
    $source = Join-Path $projectRoot $Relative
    if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
        $missing.Add($Relative)
        return
    }
    $target = Join-Path $snapshot $Relative
    New-Item -ItemType Directory -Force -Path (Split-Path -Parent $target) | Out-Null
    Copy-Item -LiteralPath $source -Destination $target
    $copied.Add($Relative)
}

Push-Location -LiteralPath $projectRoot
try {
    if (Test-Path -LiteralPath $snapshot) { Remove-Item -LiteralPath $snapshot -Recurse -Force }
    New-Item -ItemType Directory -Force -Path $snapshot | Out-Null

    # Первичное: записи и идеи (claims/*), изложение (paper/*.tex), описи коллекции, сводки.
    foreach ($name in @('blueprint.md', 'index.md')) { Copy-Record $name }
    $claims = Join-Path $projectRoot 'claims'
    if (Test-Path -LiteralPath $claims) {
        foreach ($file in Get-ChildItem -LiteralPath $claims -File -Filter *.md) { Copy-Record ('claims/' + $file.Name) }
    }
    foreach ($name in @('paper/review.tex', 'paper/exposition.tex',
                        'sources/registry.json', 'sources/catalog.md', 'sources/README.md')) {
        Copy-Record $name
    }

    # Формулировка запроса — единственный файл снимка, который входит в Git. Её место —
    # задача (класс `task`); пока её там нет, годится исходный input/prompt.md, но тогда
    # снимок зависит от каталога, который выводится из употребления.
    $prompt = @('tasks/A12/prompt.md', 'input/prompt.md') |
        Where-Object { Test-Path -LiteralPath (Join-Path $projectRoot $_) } | Select-Object -First 1
    if (-not $prompt) {
        throw 'Нет формулировки запроса: ожидается tasks/A12/prompt.md, а до переноса — input/prompt.md.'
    }
    if ($prompt -ne 'tasks/A12/prompt.md') {
        Write-Warning "Формулировка запроса взята из $prompt; перенесите её в tasks/A12/prompt.md."
    }
    Copy-Item -LiteralPath (Join-Path $projectRoot $prompt) -Destination (Join-Path $snapshot 'prompt.md')
    $copied.Add('prompt.md')

    # Полные тексты реестра обязательны: снимок без них неполон.
    $registry = Join-Path $projectRoot 'sources/registry.json'
    if (-not (Test-Path -LiteralPath $registry)) {
        throw 'Нет реестра sources/registry.json: полные тексты не сверить, снимок не собрать.'
    }
    $papers = Get-Content -LiteralPath $registry -Raw -Encoding UTF8 | ConvertFrom-Json
    foreach ($paper in $papers) {
        $names = @()
        if ($paper.tex) { $names += $paper.tex }
        if ($paper.filename) { $names += $paper.filename }
        # Запись, добавленная по одному DOI, полного текста ещё не имеет; она пропускается.
        foreach ($name in $names) {
            $file = Join-Path $projectRoot ('output/literature/' + $name)
            if (-not (Test-Path -LiteralPath $file)) {
                throw "Нет полного текста: output/literature/$name. Выполните: python tools/sources/lit.py fetch"
            }
            Copy-Record ('output/literature/' + $name)
        }
        if ($paper.filename) {
            # У сканированного PDF нет текстового слоя и потому нет файла .txt рядом.
            $text = [System.IO.Path]::ChangeExtension($paper.filename, '.txt')
            if (Test-Path -LiteralPath (Join-Path $projectRoot ('output/literature/' + $text))) {
                Copy-Record ('output/literature/' + $text)
            }
        }
    }

    # Собранный PDF берётся из output/build, а не из устаревшего input/.
    $built = @(Get-ChildItem -LiteralPath (Join-Path $projectRoot 'output/build') -Filter *.pdf -File -ErrorAction SilentlyContinue)
    foreach ($pdf in $built) { Copy-Record ('output/build/' + $pdf.Name) }

    $lines = [System.Collections.Generic.List[string]]::new()
    $lines.Add('# Снимок проекта')
    $lines.Add('')
    $lines.Add("Дата сборки: $([datetime]::Now.ToString('yyyy-MM-dd')). Каталог: output/snapshot (производный, не накопитель).")
    $lines.Add('Собран tools/host/prepare-input.ps1. Ничего не отправлено.')
    $lines.Add('')
    $lines.Add('## Файлы')
    $lines.Add('')
    foreach ($relative in $copied) {
        $hash = (Get-FileHash -LiteralPath (Join-Path $snapshot $relative) -Algorithm SHA256).Hash.ToLower()
        $lines.Add("- ``$relative`` — sha256 ``$hash``")
    }
    if ($missing.Count) {
        $lines.Add('')
        $lines.Add('## Нет файлов (ещё не созданы)')
        $lines.Add('')
        foreach ($relative in $missing) { $lines.Add("- ``$relative``") }
    }
    if (-not $built) {
        $lines.Add('')
        $lines.Add('Собранного PDF нет: output/build пуст. Сборка — tools/docs/build-review.ps1 и tools/docs/build-exposition.ps1.')
    }
    [System.IO.File]::WriteAllText((Join-Path $snapshot 'README.md'), (($lines -join "`n") + "`n"), $utf8)
    Write-Output "Снимок: output/snapshot, файлов: $($copied.Count), нет: $($missing.Count). Ничего не отправлено."
} finally {
    Pop-Location
}
