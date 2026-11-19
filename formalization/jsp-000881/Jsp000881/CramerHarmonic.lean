module

public import PrimeUniformity.CramerNormalization
public import Jsp000881.CRTIntersection
public import Jsp000881.ModelTransfer

/-!
# An elementary bound for the sum of local bad densities

Each dyadic block contributes at most one to the harmonic sum. Together
with the local union bound, this controls the Bonferroni tail without
needing a theorem about the distribution of the primes.
-/

@[expose] public section

namespace Jsp000881

open scoped BigOperators

export PrimeUniformity (harmonic_sum_pow_two_le)

/-- Uniform over admissible planes, the sum of local bad densities below
a cutoff at most `2^N` is at most `6 * (N + 1)`. -/
theorem sum_cramerBadDensity_le_dyadic (θ : PlaneIndex) (hθ : LocallyAdmissible θ)
    (Q N : ℕ) (hQ : Q ≤ (2 : ℕ) ^ N) :
    (∑ p ∈ cramerPrimeSet Q, localBadDensity θ p) ≤ 6 * ((N : ℝ) + 1) := by
  have hsub : cramerPrimeSet Q ⊆ Finset.range ((2 : ℕ) ^ N + 1) := by
    intro p hp
    have hlt : p < Q + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ ∑ p ∈ cramerPrimeSet Q, (6 : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum fun p hp => localBadDensity_le_six_div hθ (Finset.mem_filter.mp hp).2
    _ ≤ ∑ j ∈ Finset.range ((2 : ℕ) ^ N + 1), (6 : ℝ) / (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      positivity
    _ = 6 * (∑ j ∈ Finset.range ((2 : ℕ) ^ N + 1), (1 : ℝ) / (j : ℝ)) := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_sum_pow_two_le N) (by norm_num)

end Jsp000881
