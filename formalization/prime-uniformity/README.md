# Quantitative prime Gowers uniformity

The package provides the prime-uniformity input used by the Erdős #1061 proof. The required instance is `PrimeUniformity.GowersUniformityEstimate 5 1280`. The [Lean 4.34.1 compatibility layer](compat/README.md) supplies this instance using the upstream interval Gowers inverse theorem, the prime number theorem in arithmetic progressions, and the local Vaughan descent proof.

## The estimate

For sufficiently large $X$, take the difference of the prime-supported von Mangoldt weight and the finite Cramér weight on $[1,X]$. Extend it by zero to the prime field of order $p$, where $4(d+3)X<p\le 8(d+3)X$. The proposition `GowersUniformityEstimate d A` bounds the normalized Gowers cube moment by $C/(\log X)^A$, uniformly over those $p$. The moment is the $2^d$th power of the Gowers norm. [Estimate definition](PrimeUniformity/Estimate.lean)

## Main modules

| Module | Role |
| --- | --- |
| [Weights](PrimeUniformity/Weights.lean), [Gowers](PrimeUniformity/Gowers.lean), [CubeProduct](PrimeUniformity/CubeProduct.lean) | Define the weights, zero extension, and finite Gowers moments. |
| [CubeLift](PrimeUniformity/CubeLift.lean), [IntervalMoment](PrimeUniformity/IntervalMoment.lean), [IntervalNorm](PrimeUniformity/IntervalNorm.lean) | Relate interval cubes to finite-field cubes and match the normalizations. |
| [PrimePowers](PrimeUniformity/PrimePowers.lean), [StrictCutoffTransfer](PrimeUniformity/StrictCutoffTransfer.lean), [LogSavings](PrimeUniformity/LogSavings.lean) | Control proper prime powers, the endpoint of the Cramér cutoff, and the loss in logarithmic savings. |
| [Vaughan](PrimeUniformity/Vaughan.lean), [PrimeCorrelationScale](PrimeUniformity/PrimeCorrelationScale.lean) | Decompose a large prime–Cramér correlation and isolate the Type I and Type II cases. |
| [WeylInverse](PrimeUniformity/WeylInverse.lean), [DilationRecurrence](PrimeUniformity/DilationRecurrence.lean), [DyadicDilation](PrimeUniformity/DyadicDilation.lean) | Recover coefficients and rational denominators from correlations on dilated intervals. |
| [CorrelationDescent](PrimeUniformity/CorrelationDescent.lean), [UpstreamInverseReduction](PrimeUniformity/UpstreamInverseReduction.lean) | Convert bounded rank and step descent into the fixed Gowers estimate. |

The quantitative benchmark is Proposition 4.4 of Green and Sawhney. The local proof uses a native nilsequence inverse theorem and an arithmetic-progression prime estimate supplied by upstream Lean code. The [compatibility notes](compat/README.md) identify those imports and the two actual Vaughan branch proofs. [Green–Sawhney](https://arxiv.org/abs/2410.04189)

## Build

Use the [repository verification command](../../README.md#verify-the-proof) for the full proof, including this package's 4.34.1 upstream imports. For the standalone 4.33.0 package, run the following from the repository root.

```sh
cd formalization/prime-uniformity
lake exe cache get
lake build
```
