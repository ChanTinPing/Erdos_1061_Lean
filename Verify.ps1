$ErrorActionPreference = 'Stop'

function Invoke-Checked([string] $Program) {
  & $Program @args
  if ($LASTEXITCODE -ne 0) { throw "$Program failed with exit code $LASTEXITCODE" }
}

$toolchain = (Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lean-toolchain') -Raw).Trim()
$upstreamUrl = 'https://github.com/openai/math.git'
$upstreamRevision = '4eaee87548250b2682affda7d05d947c05554bae'
$work = Join-Path $PSScriptRoot '.lake/verify'
$upstream = Join-Path $work 'math'
$logPath = Join-Path $work 'proof-build.log'
New-Item -ItemType Directory -Path $work -Force | Out-Null
[IO.File]::WriteAllText($logPath, '')

Invoke-Checked elan toolchain install $toolchain
if (!(Test-Path -LiteralPath (Join-Path $upstream '.git'))) {
  Invoke-Checked git init $upstream
}
$head = git -C $upstream rev-parse --verify --quiet HEAD
if ($head -cne $upstreamRevision) {
  Invoke-Checked git -C $upstream fetch --depth 1 $upstreamUrl $upstreamRevision
  Invoke-Checked git -C $upstream checkout --detach $upstreamRevision
}

Push-Location (Join-Path $upstream 'lean')
try {
  if (!$env:LEAN_NUM_THREADS) { $env:LEAN_NUM_THREADS = '2' }
  if (!$env:LEAN_STACK_SIZE_KB) { $env:LEAN_STACK_SIZE_KB = '32768' }
  Invoke-Checked elan run $toolchain lake update
  Invoke-Checked git diff --exit-code HEAD '--' lake-manifest.json
  Invoke-Checked elan run $toolchain lake build `
    +OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse `
    +OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop `
    +OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz

  $pathPrefix = 'PROOF_LEAN_PATH='
  $pathLine = @(Invoke-Checked elan run $toolchain lake env pwsh -NoProfile -Command `
    'Write-Output "PROOF_LEAN_PATH=$env:LEAN_PATH"' | Where-Object { $_ -clike "$pathPrefix*" })
  if ($pathLine.Count -ne 1 -or $pathLine[0].Length -le $pathPrefix.Length) {
    throw 'Lake did not provide an upstream Lean search path'
  }
  $upstreamLeanPath = $pathLine[0].Substring($pathPrefix.Length)
} finally {
  Pop-Location
}

$proofBuild = Join-Path $PSScriptRoot 'formalization/prime-uniformity/compat/Build-CompatProof.ps1'
Invoke-Checked pwsh -NoProfile -File $proofBuild -ProjectRoot $PSScriptRoot `
  -UpstreamLeanPath $upstreamLeanPath 2>&1 | Tee-Object -FilePath $logPath

$audit = @(Get-Content -LiteralPath $logPath | Where-Object {
  $_ -cmatch "^'Jsp000881\.not_linear_asymptotic' depends on axioms:"
})
if ($audit.Count -ne 1 -or $audit[0] -cnotmatch '\[([^\]]*)\]\s*$') {
  throw 'Could not read the axiom audit for Jsp000881.not_linear_asymptotic'
}
$axioms = $Matches[1] -split ',\s*'
$unexpected = $axioms | Where-Object { $_ -cnotin @('propext', 'Classical.choice', 'Quot.sound') }
if ($unexpected) { throw "Unexpected axioms in the final proof: $($unexpected -join ', ')" }

Write-Output 'Verified Jsp000881.not_linear_asymptotic with only standard Lean axioms.'
