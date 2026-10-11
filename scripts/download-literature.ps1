$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$papers = Get-Content -LiteralPath (Join-Path $projectRoot 'sources/papers.json') -Raw -Encoding UTF8 | ConvertFrom-Json
$destination = Join-Path $projectRoot 'output/literature'
New-Item -ItemType Directory -Force -Path $destination | Out-Null
foreach ($paper in $papers) {
    $path = Join-Path $destination $paper.filename
    if (Test-Path -LiteralPath $path) {
        if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -eq $paper.sha256) {
            Write-Output "$($paper.code): verified existing PDF"
            continue
        }
        throw "Existing PDF differs from registry: $path. Review it before replacing."
    }
    & curl.exe -L -sS --fail --max-time 90 $paper.pdf_url -o $path
    if ($LASTEXITCODE -ne 0) { throw "Download failed: $($paper.code)" }
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $paper.sha256) {
        throw "Downloaded version differs from registry: $($paper.code). Review the new version."
    }
    Write-Output "$($paper.code): downloaded and verified"
}
