# Lean 4.34.1 compatibility and verification

The [repository verification command](../../../README.md#verify-the-proof) builds the complete proof. The two local packages also have standalone Lake targets pinned to Lean and Mathlib 4.33.0. The final theorem and its analytic imports use Lean 4.34.1.

## Pinned environment

| Dependency | Revision |
| --- | --- |
| Lean | [`v4.34.1`](../../../lean-toolchain) |
| OpenAI Math | [`4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean) |
| Mathlib | [`d13f23b723b8a846827a245b89c10fc7d3f11612`](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) |
| Other upstream packages and compatibility patches | [Lake manifest](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/lake-manifest.json) and [patch instructions](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/patches) |

[Verify.ps1](../../../Verify.ps1) checks out the upstream revision and builds these three Lake targets.

- `+OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse`
- `+OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop`
- `+OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz`

[Build-CompatProof.ps1](Build-CompatProof.ps1) compiles local modules in dependency order using the same toolchain and Lean search path. The last module is [UpstreamJspReduction.lean](../../jsp-000881/compat/UpstreamJspReduction.lean), which prints the transitive axioms of `Jsp000881.erdos_1061`.

## Where the analytic inputs enter

| Module | Role |
| --- | --- |
| [UpstreamIntervalNorm](UpstreamIntervalNorm.lean), [UpstreamNativePrimeTests](UpstreamNativePrimeTests.lean) | Match the interval normalizations and apply the upstream Gowers inverse theorem to masked nilsequence tests. |
| [UpstreamPrimePrefix](UpstreamPrimePrefix.lean) | Derive the uniform prime-prefix estimate from `residuePsi_exponential`. |
| [UpstreamPrimePreparedRankStep](UpstreamPrimePreparedRankStep.lean), [UpstreamPrimeRankIteration](UpstreamPrimeRankIteration.lean) | Prepare a test with a nonzero vertical frequency and turn uniform rank descent into step descent. |
| [UpstreamTypeIUniformFromVaughan](UpstreamTypeIUniformFromVaughan.lean), [UpstreamTypeIIVaughanBranch](UpstreamTypeIIVaughanBranch.lean) | Realize the required rank decrease in both Vaughan cases using dilation, coefficient recovery, and freezing. |
| [UpstreamFixedEstimate](UpstreamFixedEstimate.lean) | Combine the inverse theorem, the prime-prefix theorem, and the proved descent to obtain the fixed Gowers estimate. |

## Using a warm upstream build

The verifier can build the upstream modules from source. The development build used [Lake artifacts for the pinned OAI revision](https://github.com/nealmcb/openai-math-lean-tooling/blob/main/results/lake-cache-test/README.md) and compiled the external arithmetic dependencies missing from that cache. A cache-assisted build reuses compiled imports. A source rebuild or independent kernel replay provides additional verification of the imported proof objects.

For a prebuilt upstream checkout at the pinned revision, obtain the search path with `lake env` from its `lean/` directory. You can then run the local build directly. From the root of this repository, pass that search path as `$upstreamLeanPath`.

```powershell
pwsh -NoProfile -File ./formalization/prime-uniformity/compat/Build-CompatProof.ps1 `
  -ProjectRoot . -UpstreamLeanPath $upstreamLeanPath
```

The regular verification command additionally checks the final report against Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
