module

public import Jsp000881.AmbientPrime
import all Jsp000881.AmbientPrime
public import Jsp000881.RectangleCorrelation
import all Jsp000881.RectangleCorrelation
public import Jsp000881.RectangleWeightBound
import all Jsp000881.RectangleWeightBound
public import Jsp000881.RectangleErrorDecay
import all Jsp000881.RectangleErrorDecay

public section

namespace Jsp000881

open Filter Asymptotics

private theorem ambient_prime_family :
    ∃ p : ℕ → ℕ, (∀ k, (p k).Prime) ∧ ∀ᶠ k : ℕ in atTop,
      32 * primeRectangleRadius k < p k ∧ p k ≤ 64 * primeRectangleRadius k := by
  classical
  have h (k : ℕ) : ∃ p : ℕ, p.Prime ∧
      (1 ≤ k → 32 * primeRectangleRadius k < p ∧ p ≤ 64 * primeRectangleRadius k) := by
    by_cases hk : 1 ≤ k
    · obtain ⟨p, hp, h₁, h₂⟩ := exists_ambient_prime _ (primeRectangleRadius_pos hk)
      exact ⟨p, hp, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨2, Nat.prime_two, fun hk' => (hk hk').elim⟩
  choose p hprime hsize using h
  refine ⟨p, hprime, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact hsize k hk

/-- The exact original Erdős #1061 conclusion follows from the
one-dimensional quantitative true-prime U^5 estimate. -/
theorem not_linear_asymptotic_of_prime_uniformity (hUniform : QuantitativePrimeGowersUniformity) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) := by
  obtain ⟨p, hp, hsize⟩ := ambient_prime_family
  let mask := fun k : ℕ => rectangleMask (p k) ((2 : ℤ) ^ k)
  let cutoff := fun k : ℕ => primeUniformityCutoff (primeRectangleRadius k)
  have hmain := maskedCramerMass_at_rectangleRadius p (hsize.mono fun _ h => h.1)
  obtain ⟨B₀, hB₀, hweights⟩ := eventually_rectangle_weight_bound
  obtain ⟨G₀, hG₀, hU⟩ := eventually_rectangle_primeGowers_bound hUniform
  apply not_linear_asymptotic_of_weighted_prime_rectangle
  refine weightedPrimeRectangleLowerBound_of_mask (cutoff := cutoff) (mask := mask)
    (fun k nm => (rectangleMask_bounds _ _ nm).2) hmain ?_
  intro ε hε
  have hsmall := eventually_rectangle_replacement_scalar_le hB₀ hG₀ hε (hsize.mono fun _ h => h.2)
  filter_upwards [hsize, hsmall, hweights, hU, eventually_ge_atTop (40 : ℕ),
    eventually_determinantBound_lt_dyadicHeight] with k hsize hsmall hw hU hk hdet
  intro θ hθ _ j hj
  letI : Fact (p k).Prime := ⟨hp k⟩
  have hk₁ : 1 ≤ k := (by decide : (1 : ℕ) ≤ 40).trans hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk₁
  have hpR : (primeRectangleRadius k : ℤ) < (p k : ℤ) := by
    exact_mod_cast (show primeRectangleRadius k < p k by omega)
  have hdet' : determinantBound ((k : ℤ) ^ 7) < (p k : ℤ) :=
    (hdet.trans_le (dyadicHeight_le_primeRectangleRadius hk₁)).trans hpR
  have hB : 0 < B₀ * (k : ℝ) ^ 2 := mul_pos hB₀ (pow_pos hkr 2)
  have hG : 0 ≤ G₀ / (k : ℝ) ^ 40 := div_nonneg hG₀.le (pow_nonneg hkr.le 40)
  exact (masked_replacement_le hk hθ hsize.1 hdet' hB hG
    (fun n hn hr => (hw n hn hr).1) (fun n hn hr => (hw n hn hr).2)
    (hU (p k) (hp k) hsize.1 hsize.2) ⟨j, hj⟩).trans hsmall

end Jsp000881
