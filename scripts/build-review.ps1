$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location -LiteralPath $projectRoot
try {
    New-Item -ItemType Directory -Force -Path 'output' | Out-Null
    # Two passes resolve citations and numbered references, without requiring Perl.
    foreach ($pass in 1..2) {
        & pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=output review.tex
        if ($LASTEXITCODE -ne 0) { throw "pdflatex failed on pass $pass. See output/review.log." }
    }
    $warnings = Select-String -Path 'output/review.log' -Pattern 'undefined|Overfull|LaTeX Warning|Package .* Warning'
    if ($warnings) { $warnings | ForEach-Object { Write-Warning $_.Line } }
    Write-Output 'PDF: output/review.pdf'
} finally {
    Pop-Location
}
