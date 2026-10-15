param([ValidateSet('suite','all','single','multiple','unfair','investigations')][string]$Mode = 'suite', [string]$Check)
$ErrorActionPreference = 'Stop'
$candidates = @(
    $env:PYTHON,
    "$env:LOCALAPPDATA/Python/pythoncore-3.14-64/python.exe",
    'python',
    'py'
) | Where-Object { $_ }
$pythonExe = $null
foreach ($candidate in $candidates) {
    try {
        & $candidate -c 'import sys; sys.exit(0)' 2>$null
        if ($LASTEXITCODE -eq 0) { $pythonExe = $candidate; break }
    } catch { }
}
if (-not $pythonExe) { throw 'Python 3.9+ is required. Set PYTHON to its executable path.' }
$scriptArgs = @("$PSScriptRoot/verify.py", '--mode', $Mode)
if ($Check) { $scriptArgs += @('--check', $Check) }
& $pythonExe @scriptArgs
exit $LASTEXITCODE
