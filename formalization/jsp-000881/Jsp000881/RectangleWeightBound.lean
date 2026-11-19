module

public import Jsp000881.CramerNormalization
import all Jsp000881.CramerNormalization
public import Jsp000881.PrimeCutoffGrowth
import all Jsp000881.PrimeCutoffGrowth

public section

namespace Jsp000881

open Filter

private theorem abs_primeWeight_le_log_radius {k : ℕ} {n : ℤ} (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hnR : n ≤ (primeRectangleRadius k : ℤ)) :
    |primeWeight n| ≤ Real.log (primeRectangleRadius k : ℝ) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ (primeRectangleRadius k : ℝ) := by exact_mod_cast hnR
  have hR' : 1 ≤ primeRectangleRadius k := primeRectangleRadius_pos hk
  have hR : (1 : ℝ) ≤ (primeRectangleRadius k : ℝ) := by
    exact_mod_cast hR'
  unfold primeWeight
  split
  · rw [abs_of_nonneg (Real.log_nonneg hn')]
    exact Real.log_le_log (zero_lt_one.trans_le hn') hnR'
  · simpa only [abs_zero] using Real.log_nonneg hR

/-- Each of the five companion weights is bounded by the same quadratic
polynomial on all affine values used in the rectangle. -/
theorem eventually_rectangle_weight_bound :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ᶠ k : ℕ in atTop, ∀ n : ℤ,
      1 ≤ n → n ≤ (primeRectangleRadius k : ℤ) →
      |primeWeight n| ≤ B₀ * (k : ℝ) ^ 2 ∧
      |cramerWeight (primeUniformityCutoff (primeRectangleRadius k)) n| ≤ B₀ * (k : ℝ) ^ 2 := by
  let C : ℝ := Real.exp 5 * (2 : ℝ) ^ 8
  let B₀ : ℝ := 5000 + C
  have hC : 0 ≤ C := by positivity
  have hB₀ : 0 < B₀ := by positivity
  have hB₁ : (5000 : ℝ) ≤ B₀ := by dsimp only [B₀]; linarith only [hC]
  have hB₂ : C ≤ B₀ := by dsimp only [B₀]; linarith
  have hR : ∀ᶠ k : ℕ in atTop,
      1 ≤ primeRectangleRadius k ∧ Real.log (primeRectangleRadius k : ℝ) ≤ 5000 * (k : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact ⟨primeRectangleRadius_pos hk, log_primeRectangleRadius_le hk⟩
  have hcut := eventually_primeUniformityCutoff_dyadic_growth (by norm_num : (0 : ℝ) < 5000) hR
  have hN := (tendsto_atTop.mp tendsto_primeCutoffDyadicIndex) 1
  refine ⟨B₀, hB₀, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcut, hN] with k hk hcut hNk
  intro n hn hnR
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ hk' (by decide)
  let N := primeCutoffDyadicIndex k
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNk
  have hN4 : (N : ℝ) ^ 4 ≤ (k : ℝ) := by exact_mod_cast hcut.2.2
  have hN8 : (N : ℝ) ^ 8 ≤ (k : ℝ) ^ 2 := by
    calc
      _ = ((N : ℝ) ^ 4) ^ 2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hN4 2
  constructor
  · calc
      _ ≤ Real.log (primeRectangleRadius k : ℝ) := abs_primeWeight_le_log_radius hk hn hnR
      _ ≤ 5000 * (k : ℝ) := log_primeRectangleRadius_le hk
      _ ≤ 5000 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hk2 (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hB₁ (sq_nonneg _)
  · calc
      _ ≤ Real.exp 5 * (2 * max (N : ℝ) 1) ^ 8 := abs_cramerWeight_le_poly_dyadic hcut.2.1 n
      _ = C * (N : ℝ) ^ 8 := by
        dsimp only [C]
        rw [max_eq_left hN1, mul_pow, mul_assoc]
      _ ≤ C * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hN8 hC
      _ ≤ _ := mul_le_mul_of_nonneg_right hB₂ (sq_nonneg _)

/-- Taking the exponent 1280 in the prime uniformity estimate gives the
32nd power of an inverse-fortieth-power bound at the rectangle scale. -/
theorem eventually_rectangle_primeGowers_bound (hUniform : QuantitativePrimeGowersUniformity) :
    ∃ G₀ : ℝ, 0 < G₀ ∧ ∀ᶠ k : ℕ in atTop, ∀ (p : ℕ) (hp : p.Prime),
      32 * primeRectangleRadius k < p → p ≤ 64 * primeRectangleRadius k →
      letI : Fact p.Prime := ⟨hp⟩
      gowersCubeMoment 5 (primeCramerDifference (primeRectangleRadius k) p) ≤
        (G₀ / (k : ℝ) ^ 40) ^ 32 := by
  obtain ⟨C, hC, hlarge⟩ := hUniform
  let D : ℝ := C / (Real.log 2) ^ 1280
  let G₀ : ℝ := max D 1
  have hG₁ : (1 : ℝ) ≤ G₀ := le_max_right _ _
  have hDG : D ≤ G₀ := le_max_left _ _
  have hD : D ≤ G₀ ^ 32 := hDG.trans (le_self_pow₀ hG₁ (by decide))
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨G₀, zero_lt_one.trans_le hG₁, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), primeRectangleRadius_tendsto.eventually hlarge] with k hk hmain
  intro p hp hlo hhi
  letI : Fact p.Prime := ⟨hp⟩
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk₀ := zero_lt_one.trans_le hk'
  have hpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := mul_pos hk₀ hlog2
  have hlog := dyadic_log_le_log_primeRectangleRadius hk
  have hpow := pow_le_pow_left₀ hpos.le hlog 1280
  calc
    _ ≤ C / (Real.log (primeRectangleRadius k : ℝ)) ^ 1280 := hmain p hp hlo hhi
    _ ≤ C / ((k : ℝ) * Real.log 2) ^ 1280 := div_le_div_of_nonneg_left hC.le (pow_pos hpos _) hpow
    _ = D / (k : ℝ) ^ 1280 := by
      dsimp only [D]
      rw [mul_pow, div_div, mul_comm ((k : ℝ) ^ 1280) (Real.log 2 ^ 1280)]
    _ ≤ G₀ ^ 32 / (k : ℝ) ^ 1280 := div_le_div_of_nonneg_right hD (by positivity)
    _ = _ := by rw [div_pow, ← pow_mul]

end Jsp000881
