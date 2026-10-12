$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location -LiteralPath $projectRoot
try {
    New-Item -ItemType Directory -Force -Path 'input', 'input/sources', 'input-lean' | Out-Null
    foreach ($file in @('question.md', 'context.md', 'blueprint.md', 'review.tex')) {
        Copy-Item -LiteralPath $file -Destination (Join-Path 'input' $file)
    }
    foreach ($file in @('README.md', 'catalog.md', 'results.md', 'papers.json')) {
        Copy-Item -LiteralPath (Join-Path 'sources' $file) -Destination (Join-Path 'input/sources' $file)
    }
    # Preserve the relative links to full texts in the source snapshot.
    $papers = Get-Content -LiteralPath 'sources/papers.json' -Raw -Encoding UTF8 | ConvertFrom-Json
    New-Item -ItemType Directory -Force -Path 'input/output/literature' | Out-Null
    foreach ($paper in $papers) {
        $names = @()
        if ($paper.tex) { $names += $paper.tex }
        if ($paper.filename) { $names += $paper.filename }
        # A registry entry added by DOI alone has no full text yet; it is skipped.
        foreach ($name in $names) {
            $file = Join-Path 'output/literature' $name
            if (-not (Test-Path -LiteralPath $file)) { throw "Missing full text: $file. Run: python scripts/lit.py fetch" }
            Copy-Item -LiteralPath $file -Destination (Join-Path 'input/output/literature' $name)
        }
        if ($paper.filename) {
            # A scanned PDF has no text layer and hence no .txt next to it.
            $text = Join-Path 'output/literature' ([System.IO.Path]::ChangeExtension($paper.filename, '.txt'))
            if (Test-Path -LiteralPath $text) { Copy-Item -LiteralPath $text -Destination (Join-Path 'input/output/literature' (Split-Path -Leaf $text)) }
        }
    }
    Copy-Item -LiteralPath 'lean-toolchain' -Destination 'input-lean/lean-toolchain'
    # Retain exact dependency revisions; only the standalone package name changes.
    $manifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw -Encoding UTF8 | ConvertFrom-Json
    $manifest.name = 'involution-exercise'
    $json = $manifest | ConvertTo-Json -Depth 20
    [System.IO.File]::WriteAllText((Join-Path $projectRoot 'input-lean/lake-manifest.json'), $json + "`n", [System.Text.UTF8Encoding]::new($false))
    Write-Output 'Prepared input/ and input-lean/. No files were submitted.'
} finally {
    Pop-Location
}
