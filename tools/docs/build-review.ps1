# Сборка paper/review.tex: два прохода pdflatex без Perl и latexmk.
# Рабочий каталог — paper, вывод — output/build. Запуск из корня проекта:
#   powershell -NoProfile -ExecutionPolicy Bypass -File tools/docs/build-review.ps1
$ErrorActionPreference = 'Stop'
# tools/docs -> корень проекта на два уровня выше
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$name = 'review'
Push-Location -LiteralPath (Join-Path $projectRoot 'paper')
try {
    New-Item -ItemType Directory -Force -Path (Join-Path $projectRoot 'output/build') | Out-Null
    # Два прохода разрешают ссылки и номера; Perl и latexmk в системе не требуются.
    foreach ($pass in 1..2) {
        & pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '-output-directory=..\output\build' "$name.tex"
        if ($LASTEXITCODE -ne 0) { throw "pdflatex failed on pass $pass. See output/build/$name.log." }
    }
    $log = Join-Path $projectRoot "output/build/$name.log"
    if (-not (Test-Path -LiteralPath $log)) { throw "Нет журнала сборки: $log" }
    $unresolved = Select-String -Path $log -Pattern 'undefined|LaTeX Warning: Reference|LaTeX Warning: Citation'
    if ($unresolved) {
        Write-Output "Нерешённые ссылки:"
        $unresolved | ForEach-Object { Write-Output $_.Line }
    } else {
        Write-Output 'Нерешённых ссылок нет.'
    }
    $overfull = Select-String -Path $log -Pattern 'Overfull'
    if ($overfull) {
        Write-Output "Overfull:"
        $overfull | ForEach-Object { Write-Output $_.Line }
    } else {
        Write-Output 'Overfull нет.'
    }
    $pdf = Join-Path $projectRoot "output/build/$name.pdf"
    if (-not (Test-Path -LiteralPath $pdf)) { throw "PDF не создан: $pdf" }
    Write-Output "PDF: output/build/$name.pdf"
} finally {
    Pop-Location
}
