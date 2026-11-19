module

public import Mathlib.Algebra.Field.ZMod
public import PrimeUniformity.Gowers
public import PrimeUniformity.Weights

@[expose] public section

namespace PrimeUniformity

open Filter

/-- The quantitative cyclic Gowers uniformity estimate at fixed order and log-saving exponent.
The constant may depend on these two parameters and is uniform in the prime modulus. The
bound concerns the normalized cube moment, the `2^order`-th power of the Gowers norm. -/
def GowersUniformityEstimate (order exponent : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ (p : ℕ) (hp : p.Prime), 4 * (order + 3) * X < p → p ≤ 8 * (order + 3) * X →
      letI : Fact p.Prime := ⟨hp⟩
      gowersCubeMoment order (primeCramerDifference X p) ≤ C / (Real.log (X : ℝ)) ^ exponent

/-- Quantitative prime Gowers uniformity for every fixed order at least two and every
fixed logarithmic saving. -/
def QuantitativePrimeGowersUniformity : Prop :=
  ∀ order : ℕ, 2 ≤ order → ∀ exponent : ℕ, GowersUniformityEstimate order exponent

end PrimeUniformity
