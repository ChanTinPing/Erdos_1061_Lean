# Erdős #1061 counting argument

This package formalizes the construction and counting argument for JSP-000881. The final theorem is `Jsp000881.erdos_1061` in [UpstreamJspReduction.lean](compat/UpstreamJspReduction.lean). It rules out a positive linear asymptotic for the original ordered-pair count. Start with the [repository verification command](../../README.md#verify-the-proof) to build it with Lean 4.34.1.

## Proof structure

| Module | Role |
| --- | --- |
| [OriginalProblem](Jsp000881/OriginalProblem.lean) | Defines the reference count and checks that it agrees pointwise with the proof's count. |
| [Plane](Jsp000881/Plane.lean), [Solutions](Jsp000881/Solutions.lean) | Formalize the integer planes and inject ordered fresh prime sextuples into ordered solutions. |
| [ParameterSieve](Jsp000881/ParameterSieve.lean), [Counting](Jsp000881/Counting.lean) | Retain a positive proportion of locally admissible parameter triples and bound duplicates from plane intersections. |
| [Heights](Jsp000881/Heights.lean), [Rectangles](Jsp000881/Rectangles.lean), [Scaled](Jsp000881/Scaled.lean) | Establish the explicit rectangles, height and perimeter bounds, and the superlinear lower bound on dyadic scales. |
| [ResidueRectangles](Jsp000881/ResidueRectangles.lean), [Products](Jsp000881/Products.lean), [CramerMass](Jsp000881/CramerMass.lean) | Obtain the uniform positive Cramér main term using rectangle residue counts, finite local factors, and truncated inclusion-exclusion. |
| [GowersIteration](Jsp000881/GowersIteration.lean), [TriangleCutoff](Jsp000881/TriangleCutoff.lean), [RectangleCorrelation](Jsp000881/RectangleCorrelation.lean) | Bound each of the six replacements by five Cauchy–Schwarz steps and use triangular interval weights to control the Fourier loss. |
| [PrimeReduction](Jsp000881/PrimeReduction.lean) | Derives the negative answer from the fixed prime-uniformity estimate at order 5 and exponent 1280. |
| [UpstreamJspReduction](compat/UpstreamJspReduction.lean) | Supplies the estimate using the two Vaughan descent branches and concludes the original statement. |

The restriction to denominator $q=1$ applies to the constructed family of solutions. The target count ranges over every ordered pair of positive integers. A sufficiently large lower bound from this family rules out a linear asymptotic for the full count.

The [prime-counting notes](prime-estimate.md) give the scales and the link to the analytic input. The [development notes](exploration.md) describe the fixed-denominator construction and earlier exploratory routes.

## Modular build

The local Lake package pins Lean and Mathlib 4.33.0. This target builds the counting modules, including the statement correspondence. The unconditional endpoint uses the [4.34.1 compatibility build](../prime-uniformity/compat/README.md).

```sh
cd formalization/jsp-000881
lake exe cache get
lake build
```

[Eric Li, *A resolution of Erdős Problem 1061 on the sum-of-divisors function*, arXiv:2606.25849v1](https://arxiv.org/abs/2606.25849v1)
