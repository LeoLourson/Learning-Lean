$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($lakeCommand) {
    $lakeExe = $lakeCommand.Source
} else {
    $lakeExe = Join-Path $env:USERPROFILE '.elan/bin/lake.exe'
}
if (-not (Test-Path -LiteralPath $lakeExe)) { throw 'Lean/Lake not found. Install elan or fix PATH.' }
Push-Location -LiteralPath $projectRoot
try {
    foreach ($file in @('README.md', 'AGENTS.md', 'question.md', 'context.md', 'review.tex', 'blueprint.md', 'sources/README.md', '.gitignore', 'Scratch.lean', 'Search.lean', 'Target.lean')) {
        if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { throw "Missing required file: $file" }
    }
    & $lakeExe build
    if ($LASTEXITCODE -ne 0) { throw 'lake build failed.' }
    foreach ($file in @('Target.lean', 'Scratch.lean', 'Search.lean')) {
        $result = & $lakeExe env lean $file 2>&1
        $code = $LASTEXITCODE
        $result | ForEach-Object { Write-Output $_ }
        if ($code -ne 0) { throw "Lean failed: $file" }
        if (($result -join "`n") -match 'sorryAx|declaration uses .sorry.') { throw "Incomplete proof: $file" }
    }
    & git check-ignore output/probe.pdf
    if ($LASTEXITCODE -ne 0) { throw 'output/ is not ignored.' }
    Write-Output 'Project checks passed. The separate Aristotle exercise intentionally contains one sorry.'
} finally {
    Pop-Location
}
