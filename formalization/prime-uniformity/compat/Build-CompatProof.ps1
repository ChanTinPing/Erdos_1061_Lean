param(
  [Parameter(Mandatory)][string] $ProjectRoot,
  [Parameter(Mandatory)][string] $UpstreamLeanPath,
  [switch] $PlanOnly
)
$ErrorActionPreference = 'Stop'
$prime = (Resolve-Path -LiteralPath (Join-Path $ProjectRoot 'formalization/prime-uniformity')).ProviderPath
$jsp = (Resolve-Path -LiteralPath (Join-Path $ProjectRoot 'formalization/jsp-000881')).ProviderPath
$build = Join-Path $prime '.lake/compat-v4.34-final'
$stage = Join-Path $build 'source'
$out = Join-Path $build 'lib/lean'
$env:LEAN_PATH = @($out, $UpstreamLeanPath) -join [IO.Path]::PathSeparator
$env:LEAN_NUM_THREADS = '1'
$env:LEAN_STACK_SIZE_KB = '32768'
$seen = [System.Collections.Generic.HashSet[string]]::new()
$pattern = '^[\t ]*(?:(?:public|private|meta)[\t ]+)*import[\t ]+(?:(?:all|public|private|meta)[\t ]+)*([\w.]+)'
function Build-Module([string] $name) {
  if (!$seen.Add($name)) { return }
  $stem = $name.Replace('.', '/')
  $root = if ($name.StartsWith('Jsp000881.')) { $jsp } else { $prime }
  $file = Join-Path $root "$stem.lean"
  if (!(Test-Path -LiteralPath $file -PathType Leaf)) {
    if ($name -eq 'UpstreamJspReduction') { $root = $jsp }
    elseif ($name -notmatch '^(?:PrimeUniformity\.)?Upstream') { return }
    $compatFile = ($name -split '\.')[-1] + '.lean'
    $file = Join-Path $root "compat/$compatFile"
    $root = $stage
  }
  foreach ($line in Get-Content -LiteralPath $file -Encoding UTF8) {
    if ($line -match $pattern) { Build-Module $Matches[1] }
  }
  $obj = Join-Path $out "$stem.olean"
  if ($PlanOnly) {
    Write-Output "$name  $file  $obj"
    return
  }
  if ($root -eq $stage) {
    $stagedFile = Join-Path $stage "$stem.lean"
    New-Item -ItemType Directory -Path (Split-Path -Parent $stagedFile) -Force | Out-Null
    Copy-Item -LiteralPath $file -Destination $stagedFile
    $file = $stagedFile
  }
  New-Item -ItemType Directory -Path (Split-Path -Parent $obj) -Force | Out-Null
  Push-Location -LiteralPath $root
  try {
    elan run leanprover/lean4:v4.34.1 lean -j 1 -o $obj "$stem.lean"
    if ($LASTEXITCODE -ne 0) { throw "Lean failed for $name" }
  } finally {
    Pop-Location
  }
}
Build-Module 'UpstreamJspReduction'
