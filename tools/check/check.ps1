<#
.SYNOPSIS
    Единая проверка проекта: документы, Lean, реестр аксиом, раскладка, тесты.

.DESCRIPTION
    Шаги:
      1. обязательные файлы нового дерева;
      2. lake build;
      3. lake env lean для Target.lean, Scratch.lean, Search.lean и поиск sorry в выводе;
      4. сборка output/generated/Axioms.lean и сверка множества аксиом с допустимым;
      5. python tools/check/structure.py;
      6. python tools/state/build_index.py --check;
      7. python tools/state/gen_status.py --check;
      8. python -m unittest discover -s tools/tests;
      9. python tools/host/harness.py check;
     10. git check-ignore output/probe.pdf и git diff --check.

    Допустимые аксиомы: propext, Classical.choice, Quot.sound.

.NOTES
    Windows PowerShell 5.1 и $ErrorActionPreference = 'Stop': любая строка stderr
    от lake или lean превращается в NativeCommandError ещё до разбора вывода.
    Поэтому все нативные вызовы идут через Invoke-Native, который локально
    ставит 'Continue' и возвращает объект { Code, Lines }. Если в PATH есть
    pwsh (PowerShell 7), удобнее запускать скрипт им: pwsh -NoProfile -File
    tools/check/check.ps1.
#>
[CmdletBinding()]
param(
    [switch]$Plan,
    [switch]$SkipBuild
)

$ErrorActionPreference = 'Stop'
$LASTEXITCODE = 0

$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$script:Failures = New-Object System.Collections.Generic.List[string]
$AllowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')

function Write-Step {
    param([string]$Text)
    Write-Host ''
    Write-Host "== $Text =="
}

function Add-Failure {
    param([string]$Text)
    Write-Host "  [!] $Text" -ForegroundColor Red
    $script:Failures.Add($Text) | Out-Null
}

function Add-Ok {
    param([string]$Text)
    Write-Host "  [ok] $Text" -ForegroundColor Green
}

function Add-Note {
    param([string]$Text)
    Write-Host "  [i] $Text"
}

function Invoke-Native {
    param(
        [Parameter(Mandatory)][string]$FilePath,
        [string[]]$Arguments = @()
    )
    $previous = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    $lines = @()
    $code = 0
    try {
        # Строка stderr нативного вызова приходит объектом ErrorRecord: его
        # ToString() на многострочном выводе даёт «RemoteException», поэтому
        # берём текст из Exception.Message.
        $lines = @(& $FilePath @Arguments 2>&1 | ForEach-Object {
                if ($_ -is [System.Management.Automation.ErrorRecord] -and $_.Exception) { $_.Exception.Message }
                else { "$_" }
            })
        if ($null -ne $LASTEXITCODE) { $code = [int]$LASTEXITCODE }
    } catch {
        $lines = @("$($_.Exception.Message)")
        $code = 1
    } finally {
        $ErrorActionPreference = $previous
    }
    return [pscustomobject]@{ Code = $code; Lines = $lines }
}

# --- поиск исполняемых файлов ---------------------------------------------

function Resolve-Tool {
    param([string[]]$Names, [string[]]$Probe = @('--version'))
    foreach ($name in $Names) {
        $command = Get-Command $name -ErrorAction SilentlyContinue
        if (-not $command) { continue }
        $result = Invoke-Native -FilePath $command.Source -Arguments $Probe
        if ($result.Code -eq 0) { return $command.Source }
    }
    return $null
}

$lakeExe = Resolve-Tool -Names @('lake') -Probe @('--version')
if (-not $lakeExe) {
    # elan ставит lake в ~/.elan/bin; на Linux имя без .exe, а USERPROFILE пуст.
    foreach ($base in @($env:USERPROFILE, $env:HOME)) {
        if (-not $base -or $lakeExe) { continue }
        foreach ($name in @('.elan/bin/lake.exe', '.elan/bin/lake')) {
            $candidate = Join-Path $base $name
            if (Test-Path -LiteralPath $candidate) { $lakeExe = $candidate; break }
        }
    }
}
$pythonExe = Resolve-Tool -Names @('python', 'python3') -Probe @('--version')

$requiredFiles = @(
    'AGENTS.md', 'README.md', 'CLAUDE.md', 'LAYOUT.md', 'FACETS.md', '.gitignore', '.mcp.json',
    'lakefile.toml', 'lean-toolchain', 'lake-manifest.json',
    'Involution.lean', 'Scratch.lean', 'Search.lean', 'Target.lean',
    'claims/question.md', 'index.md', 'blueprint.md',
    'sources/README.md', 'sources/registry.json', 'sources/catalog.md',
    'paper/review.tex', 'paper/exposition.tex', 'paper/generated/status.tex',
    'tools/state/build_index.py', 'tools/state/gen_status.py', 'tools/state/gen_ledger.py',
    'tools/check/structure.py', 'tools/check/check.ps1',
    'tools/host/harness.py'
)

if ($Plan) {
    Write-Host "План проверки для: $projectRoot"
    Write-Host "  lake:   $(if ($lakeExe) { $lakeExe } else { 'не найден' })"
    Write-Host "  python: $(if ($pythonExe) { $pythonExe } else { 'не найден' })"
    $index = 0
    foreach ($step in @(
            "обязательные файлы нового дерева ($($requiredFiles.Count) шт.)",
            'lake build',
            'lake env lean Target.lean / Scratch.lean / Search.lean, поиск sorry',
            'python tools/state/gen_ledger.py; lake env lean output/generated/Axioms.lean; сверка аксиом',
            'python tools/check/structure.py',
            'python tools/state/build_index.py --check',
            'python tools/state/gen_status.py --check',
            'python -m unittest discover -s tools/tests',
            'python tools/host/harness.py check',
            'git check-ignore output/probe.pdf; git diff --check'
        )) {
        $index++
        Write-Host ("  {0,2}. {1}" -f $index, $step)
    }
    exit 0
}

Push-Location -LiteralPath $projectRoot
try {
    # --- 1. обязательные файлы
    Write-Step '1. Обязательные файлы'
    $missing = @()
    foreach ($file in $requiredFiles) {
        if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { $missing += $file }
    }
    if ($missing.Count -gt 0) {
        foreach ($file in $missing) { Add-Failure "нет файла: $file" }
    } else {
        Add-Ok "на месте все $($requiredFiles.Count) файлов"
    }

    if (-not $lakeExe) { Add-Failure 'Lean/Lake не найден: установи elan или поправь PATH' }
    if (-not $pythonExe) { Add-Failure 'python не найден' }

    # --- 2. сборка
    Write-Step '2. lake build'
    if ($SkipBuild) {
        Add-Note 'пропущено по -SkipBuild'
    } elseif ($lakeExe) {
        $build = Invoke-Native -FilePath $lakeExe -Arguments @('build')
        $build.Lines | ForEach-Object { Write-Host "    $_" }
        if ($build.Code -ne 0) {
            Add-Failure "lake build завершился с кодом $($build.Code)"
        } else {
            Add-Ok 'lake build прошёл'
            $sorryLines = @($build.Lines | Where-Object { $_ -match "declaration uses 'sorry'|sorryAx" })
            if ($sorryLines.Count -gt 0) {
                foreach ($line in $sorryLines) { Add-Failure "сборка сообщает о sorry: $line" }
            } else {
                Add-Ok 'в выводе сборки нет sorry'
            }
        }
    }

    # --- 3. пробы
    Write-Step '3. Пробы Lean'
    if ($SkipBuild) {
        Add-Note 'пропущено по -SkipBuild'
    } elseif ($lakeExe) {
        foreach ($file in @('Target.lean', 'Scratch.lean', 'Search.lean')) {
            if (-not (Test-Path -LiteralPath $file -PathType Leaf)) {
                Add-Failure "нет файла пробы: $file"
                continue
            }
            $probe = Invoke-Native -FilePath $lakeExe -Arguments @('env', 'lean', $file)
            $probe.Lines | ForEach-Object { Write-Host "    $_" }
            if ($probe.Code -ne 0) {
                Add-Failure "lake env lean $file завершился с кодом $($probe.Code)"
            } elseif (($probe.Lines -join "`n") -match "sorryAx|declaration uses 'sorry'") {
                Add-Failure "неполное доказательство: $file"
            } else {
                Add-Ok "$file чист"
            }
        }
    }

    # --- 4. реестр аксиом
    Write-Step '4. Реестр аксиом'
    if ($pythonExe) {
        $ledger = Invoke-Native -FilePath $pythonExe -Arguments @('tools/state/gen_ledger.py')
        $ledger.Lines | ForEach-Object { Write-Host "    $_" }
        if ($ledger.Code -ne 0) { Add-Failure 'tools/state/gen_ledger.py завершился с ошибкой' }
        $ledgerPath = 'output/generated/Axioms.lean'
        if (-not (Test-Path -LiteralPath $ledgerPath -PathType Leaf)) {
            Add-Failure "нет файла реестра: $ledgerPath"
        } elseif (Test-Path -LiteralPath $ledgerPath -PathType Leaf) {
            $prints = @(Select-String -LiteralPath $ledgerPath -Pattern '^#print axioms' -ErrorAction SilentlyContinue)
            if ($prints.Count -eq 0) {
                Add-Note 'в реестре нет строк #print axioms: записей с final: true или proved-* пока нет'
            } elseif ($SkipBuild) {
                Add-Note 'сверка аксиом пропущена по -SkipBuild'
            } elseif ($lakeExe) {
                $audit = Invoke-Native -FilePath $lakeExe -Arguments @('env', 'lean', $ledgerPath)
                $audit.Lines | ForEach-Object { Write-Host "    $_" }
                if ($audit.Code -ne 0) {
                    Add-Failure "lake env lean $ledgerPath завершился с кодом $($audit.Code)"
                } else {
                    $found = New-Object System.Collections.Generic.HashSet[string]
                    foreach ($line in $audit.Lines) {
                        $match = [regex]::Match($line, 'depends on axioms:\s*\[([^\]]*)\]')
                        if ($match.Success) {
                            foreach ($item in ($match.Groups[1].Value -split ',')) {
                                $name = $item.Trim()
                                if ($name) { $found.Add($name) | Out-Null }
                            }
                        }
                    }
                    $printed = 0
                    $sorryLines = 0
                    foreach ($line in $audit.Lines) {
                        if ($line -match 'depends on axioms:') { $printed++ }
                        if ($line -match 'sorryAx') { $sorryLines++ }
                    }
                    if ($sorryLines -gt 0) {
                        Add-Failure "реестр использует sorryAx (строк: $sorryLines)"
                    }
                    if ($printed -lt $prints.Count) {
                        Add-Failure "реестр: напечатано $printed ответов на $($prints.Count) строк #print axioms"
                    }
                    $extra = @($found | Where-Object { $AllowedAxioms -notcontains $_ })
                    if ($extra.Count -gt 0) {
                        foreach ($name in $extra) { Add-Failure "недопустимая аксиома: $name" }
                    } else {
                        $list = if ($found.Count -gt 0) { ($found | Sort-Object) -join ', ' } else { 'нет' }
                        Add-Ok "аксиомы допустимы: $list"
                    }
                }
            }
        }
    }

    # --- 5. раскладка
    Write-Step '5. tools/check/structure.py'
    if ($pythonExe) {
        $structure = Invoke-Native -FilePath $pythonExe -Arguments @('tools/check/structure.py')
        $structure.Lines | ForEach-Object { Write-Host "  $_" }
        if ($structure.Code -ne 0) {
            Add-Failure "structure.py нашёл нарушения (код $($structure.Code))"
        } else {
            Add-Ok 'инварианты раскладки выполнены'
        }
    }

    # --- 6. свежесть index.md и blueprint.md
    Write-Step '6. tools/state/build_index.py --check'
    if ($pythonExe) {
        $indexCheck = Invoke-Native -FilePath $pythonExe -Arguments @('tools/state/build_index.py', '--check')
        $indexCheck.Lines | ForEach-Object { Write-Host "    $_" }
        if ($indexCheck.Code -ne 0) {
            Add-Failure 'index.md или blueprint.md устарели: запусти python tools/state/build_index.py'
        } else {
            Add-Ok 'index.md и blueprint.md свежие'
        }
    }

    # --- 7. свежесть status.tex
    Write-Step '7. tools/state/gen_status.py --check'
    if ($pythonExe) {
        $statusCheck = Invoke-Native -FilePath $pythonExe -Arguments @('tools/state/gen_status.py', '--check')
        $statusCheck.Lines | ForEach-Object { Write-Host "    $_" }
        if ($statusCheck.Code -ne 0) {
            Add-Failure 'paper/generated/status.tex устарел: запусти python tools/state/gen_status.py'
        } else {
            Add-Ok 'paper/generated/status.tex свежий'
        }
    }

    # --- 8. тесты
    Write-Step '8. python -m unittest discover -s tools/tests'
    if ($pythonExe) {
        if (-not (Test-Path -LiteralPath 'tools/tests')) {
            Add-Failure 'нет каталога tools/tests'
        } else {
            $tests = Invoke-Native -FilePath $pythonExe -Arguments @('-m', 'unittest', 'discover', '-s', 'tools/tests')
            $tests.Lines | ForEach-Object { Write-Host "    $_" }
            if ($tests.Code -ne 0) {
                Add-Failure "тесты не прошли (код $($tests.Code))"
            } else {
                Add-Ok 'тесты прошли'
            }
        }
    }

    # --- 9. адаптер Harness
    Write-Step '9. tools/host/harness.py check'
    if ($pythonExe) {
        if (-not (Test-Path -LiteralPath 'tools/host/harness.py' -PathType Leaf)) {
            Add-Failure 'нет файла tools/host/harness.py'
        } else {
            $harness = Invoke-Native -FilePath $pythonExe -Arguments @('tools/host/harness.py', 'check')
            $harness.Lines | ForEach-Object { Write-Host "    $_" }
            if ($harness.Code -ne 0) {
                Add-Failure 'harness.py check нашёл расхождения'
            } else {
                Add-Ok 'производные Harness свежие'
            }
        }
    }

    # --- 10. Git
    Write-Step '10. Git'
    $git = Get-Command git -ErrorAction SilentlyContinue
    if (-not $git) {
        Add-Note 'git не найден: проверки репозитория пропущены'
    } else {
        $ignore = Invoke-Native -FilePath $git.Source -Arguments @('check-ignore', 'output/probe.pdf')
        if ($ignore.Code -ne 0) {
            Add-Failure 'каталог output/ не исключён из Git'
        } else {
            Add-Ok 'output/ исключён из Git'
        }
        $diff = Invoke-Native -FilePath $git.Source -Arguments @('diff', '--check')
        $diff.Lines | ForEach-Object { Write-Host "    $_" }
        if ($diff.Code -ne 0) {
            Add-Failure 'git diff --check нашёл замечания'
        } else {
            Add-Ok 'git diff --check чист'
        }
    }
} finally {
    Pop-Location
}

Write-Host ''
if ($script:Failures.Count -gt 0) {
    Write-Host "Проверки не пройдены: нарушений $($script:Failures.Count)." -ForegroundColor Red
    exit 1
}
Write-Host 'Все проверки пройдены.' -ForegroundColor Green
exit 0
