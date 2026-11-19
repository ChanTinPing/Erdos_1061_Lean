# Erdős Problem #1061 in Lean 4

This repository gives an unconditional Lean proof that the number of ordered solutions to Erdős Problem #1061 has no positive linear asymptotic. The corresponding Justin Sun Prize catalog entry is **JSP-000881**. [Original problem](https://www.erdosproblems.com/1061) · [Prize catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000881)

## Statement

Let $\sigma(n)$ be the sum of the positive divisors of $n$. For a real cutoff $x$, let $S(x)$ count the ordered pairs of positive integers $(a,b)$ with $a+b\le x$ and $\sigma(a)+\sigma(b)=\sigma(a+b)$. The original question asks whether $S(x)\sim cx$ as $x\to\infty$ for some real $c>0$. The Lean proof gives the negative answer.

```lean
theorem not_linear_asymptotic : ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x)
```

The fully qualified theorem is [`Jsp000881.not_linear_asymptotic`](formalization/jsp-000881/compat/UpstreamJspReduction.lean#L44-L49). Its [`S` definition](formalization/jsp-000881/Jsp000881/Reduction.lean#L21-L27) counts the same ordered pairs as the [pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/b576d527b271b936f9e61c0e367c302d7386bc80/FormalConjectures/ErdosProblems/1061.lean). The positive lower bounds on both coordinates come from `Finset.Icc 1 ⌊x⌋₊`, and the outer negation answers the existence question for all positive real constants.

## Proof outline and attribution

The mathematical solution is due to **Eric Li**, *A resolution of Erdős Problem 1061 on the sum-of-divisors function*, arXiv:2606.25849v1, Theorem 1.1. Li proves a stronger growth result at every fixed logarithmic scale. This project formalizes the original negative answer using a fixed-denominator family from Li's construction. [Paper](https://arxiv.org/abs/2606.25849v1)

1. Construct a family of integer planes carrying six affine forms. Six distinct primes in the prescribed order give an ordered solution to the divisor-sum equation. The parameter sieve and intersection bounds control local obstructions and duplicate counts. [Construction and counting package](formalization/jsp-000881/README.md)
2. Establish a positive main term for the Cramér model and transfer it to the actual prime weights in the six forms. The transfer uses the fixed estimate `PrimeUniformity.GowersUniformityEstimate 5 1280` for the normalized fifth-order Gowers cube moment. The resulting count rules out $S(x)\sim cx$. [Counting reduction](formalization/jsp-000881/Jsp000881/PrimeReduction.lean)
3. Discharge the prime-uniformity estimate with the interval Gowers inverse theorem, the prime number theorem in arithmetic progressions, and the Vaughan Type I and Type II rank-descent arguments developed here. The final entry point supplies both descent branches to the counting reduction. [Prime-uniformity package](formalization/prime-uniformity/) · [Proof dependencies](formalization/prime-uniformity/compat/README.md)

The Lean formalization project is maintained by [@ChanTinPing](https://github.com/ChanTinPing). It uses pinned Lean developments from [OpenAI Math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean) and [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612). The adapted scalar Weyl argument carries its original attribution and [Apache 2.0 license text](formalization/prime-uniformity/LICENSE-APACHE).

## Reproduce the complete proof

Use **Lean 4.34.1** through Elan, Git, and PowerShell 7 (`pwsh`). The complete proof uses `openai/math` at `4eaee87548250b2682affda7d05d947c05554bae`, whose [Lake manifest](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/lake-manifest.json) pins Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` and the other analysis dependencies. The v4.33.0 Lake targets in the two subpackages cover earlier modular build targets. Use the v4.34.1 commands below to check the unconditional theorem.

In PowerShell, start at the root of this proof repository. Check out the selected 40-character proof commit before running these commands and record the output of `git rev-parse HEAD` with your verification log.

```powershell
$proofRepo = (Get-Location).Path
git rev-parse HEAD
elan toolchain install leanprover/lean4:v4.34.1

$oaiRepo = Join-Path (Split-Path $proofRepo -Parent) 'oai-math-1061'
git clone https://github.com/openai/math.git $oaiRepo
if ($LASTEXITCODE -ne 0) { throw 'Could not clone openai/math' }
git -C $oaiRepo checkout --detach 4eaee87548250b2682affda7d05d947c05554bae
if ($LASTEXITCODE -ne 0) { throw 'Could not check out the pinned openai/math revision' }

Push-Location (Join-Path $oaiRepo 'lean')
try {
  $env:LEAN_NUM_THREADS = '2'
  $env:LEAN_STACK_SIZE_KB = '32768'
  lake update
  if ($LASTEXITCODE -ne 0) { throw 'Upstream dependency setup failed' }
  git diff --exit-code -- lake-manifest.json
  if ($LASTEXITCODE -ne 0) { throw 'Upstream dependency pins changed' }
  lake build `
    +OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse `
    +OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop `
    +OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz
  if ($LASTEXITCODE -ne 0) { throw 'Upstream Lean build failed' }
  $upstreamLeanPath = lake env pwsh -NoProfile -Command '$env:LEAN_PATH'
  if ($LASTEXITCODE -ne 0 -or !$upstreamLeanPath) { throw 'Could not obtain the upstream Lean path' }
} finally {
  Pop-Location
}
```

`lake update` applies the upstream compatibility patches. A cold build of the three upstream targets can take substantial time. The [compatibility notes](formalization/prime-uniformity/compat/README.md) describe how the development build restored upstream Lake artifacts and built the remaining dependencies. The local script rebuilds the proof's local import closure in dependency order.

```powershell
$log = & pwsh -NoProfile -File formalization/prime-uniformity/compat/Build-CompatProof.ps1 `
  -ProjectRoot $proofRepo -UpstreamLeanPath $upstreamLeanPath
$buildExit = $LASTEXITCODE
$log | Tee-Object -FilePath proof-build.log
if ($buildExit -ne 0) { throw 'Lean proof build failed' }

$audit = $log | Where-Object { $_ -match "^'Jsp000881\.not_linear_asymptotic' depends on axioms:" }
if (@($audit).Count -ne 1 -or $audit -notmatch '\[([^\]]*)\]$') {
  throw 'Could not read the axiom audit for the final theorem'
}
$axioms = $Matches[1] -split ',\s*'
$unexpected = $axioms | Where-Object { $_ -notin @('propext', 'Classical.choice', 'Quot.sound') }
if ($unexpected) { throw "Unexpected axioms in the final proof: $($unexpected -join ', ')" }
```

The [development build record](formalization/prime-uniformity/compat/README.md#同一工具链中的原题入口) reports `propext`, `Classical.choice`, and `Quot.sound` for `#print axioms Jsp000881.not_linear_asymptotic`. This Lean command checks transitive dependencies, including imported proofs. A used placeholder would appear as `sorryAx`. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

## Review information for JSP-000881

| Item | Reference |
| --- | --- |
| Contribution | Lean formalization of the original negative answer |
| Mathematical solution | [Eric Li, arXiv:2606.25849v1, Theorem 1.1](https://arxiv.org/abs/2606.25849v1) |
| Proof repository and branch | `ChanTinPing/Erdos_1061_Lean`, `main` |
| Proof revision | Use the full public commit SHA of the proof version being reviewed |
| Formal target | [`Jsp000881.not_linear_asymptotic`](formalization/jsp-000881/compat/UpstreamJspReduction.lean#L44-L49) |
| Reproduction and audit | [Build and verify](#reproduce-the-complete-proof) |

The public import preserves the `formalization/` tree from the development commit `e64c8167718c1e955c7a29e1a74d87c43aaa00ef` byte for byte. Its Git tree ID is `93c26ae6027def810c2cb0a594befe97eb2ab106`, which can be checked with `git rev-parse HEAD:formalization`. Use the public repository's commit SHA for the [official proof-reference submission](https://github.com/TheJustinSunPrize/awards/blob/main/.github/PULL_REQUEST_TEMPLATE.md).
