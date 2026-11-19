module

public import Jsp000881.PrimeReduction
public import PrimeUniformity.CorrelationDescent

public section

namespace Jsp000881

open Filter Asymptotics

/-- A fifth-order interval inverse theorem and stretched-exponential
prime–Cramér orthogonality against its tests suffice for the original count. -/
theorem not_linear_asymptotic_of_inverse_and_correlation
    (tests : ℕ → ℝ → Set (ℤ → ℂ))
    (hinverse : PrimeUniformity.IntervalCorrelationInverse 5 tests)
    (horthogonal : ∃ b M : ℝ, 0 < b ∧ 0 < M ∧ ∀ᶠ X : ℕ in atTop,
      ∀ p : ℝ, p ≤ Real.log (X : ℝ) ^ b → ∀ F ∈ tests X p,
        PrimeUniformity.intervalCorrelation X (PrimeUniformity.strictVonMangoldtCramerDifference X) F ≤
          M * Real.exp (-(Real.log (X : ℝ) ^ b))) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_prime_uniformity
    (PrimeUniformity.gowersUniformityEstimate_of_inverse_and_correlation 4 1280 tests hinverse horthogonal)

/-- Use the progression theorem at the endpoint of the fourth-step inverse
tests. The only structural input is the quantitative step descent. -/
theorem not_linear_asymptotic_of_inverse_and_step_descent
    (tests : ℕ → ℕ → ℝ → Set (ℤ → ℂ))
    (hprime : PrimeUniformity.UniformPrimePrefixEstimate)
    (hinverse : PrimeUniformity.IntervalCorrelationInverse 5 (tests 4))
    (hmono : ∀ X, Monotone (tests 4 X))
    (hzero : ∀ X p, tests 0 X p ⊆ PrimeUniformity.ProgressionCombination X p)
    (hdescent : PrimeUniformity.PrimeCramerStepDescent 4 tests) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_inverse_and_correlation (tests 4) hinverse
    (PrimeUniformity.eventually_prime_cramer_orthogonal_of_descent tests hprime hmono hzero hdescent)

end Jsp000881
