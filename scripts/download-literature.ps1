$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
# Restores the LaTeX sources and PDFs listed in sources/papers.json and verifies checksums.
& python (Join-Path $projectRoot 'scripts/lit.py') fetch
if ($LASTEXITCODE -ne 0) { throw 'Some full texts were not restored; see the lines marked with an error above.' }
