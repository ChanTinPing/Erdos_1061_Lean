module

public import Jsp000881.RectangleRadius
import all Jsp000881.RectangleRadius

/-!
# Decay of the scalar replacement error

The ambient group contributes a factor quadratic in its size. After
scaling by the rectangle area, the five weights and the uniformity bound
leave a factor inverse quadratic in the scale index.
-/

public section

namespace Jsp000881

open Filter

private theorem radius_replacement_scalar_eq (B₀ G₀ : ℝ) {k : ℕ} (hk : (0 : ℝ) < (k : ℝ)) :
    (64 * (primeRectangleRadius k : ℝ)) ^ 2 * (B₀ * (k : ℝ) ^ 2) ^ 5 * (G₀ / (k : ℝ) ^ 40) =
      (((64 * 4000 : ℝ) ^ 2 * B₀ ^ 5 * G₀) / (k : ℝ) ^ 2) * (4 : ℝ) ^ k := by
  let K := (64 * 4000 : ℝ) ^ 2 * B₀ ^ 5 * G₀
  have htwo : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    calc
      _ = (2 : ℝ) ^ (k * 2) := (pow_mul _ _ _).symm
      _ = (2 : ℝ) ^ (2 * k) := by rw [Nat.mul_comm k 2]
      _ = _ := by norm_num [pow_mul]
  have hcancel : (k : ℝ) ^ 38 / (k : ℝ) ^ 40 = 1 / (k : ℝ) ^ 2 := by
    apply (div_eq_div_iff (pow_ne_zero _ hk.ne') (pow_ne_zero _ hk.ne')).mpr
    rw [one_mul, ← pow_add]
  rw [primeRectangleRadius_cast]
  calc
    _ = K * ((k : ℝ) ^ 38 / (k : ℝ) ^ 40) * (4 : ℝ) ^ k := by
      simp only [mul_pow, htwo, K, div_eq_mul_inv]
      ring
    _ = _ := by rw [hcancel]; simp only [K, div_eq_mul_inv, one_mul]

/-- At every sufficiently large scale, the scalar error is at most the
requested fraction of the rectangle's natural area. -/
theorem eventually_rectangle_replacement_scalar_le {p : ℕ → ℕ} {B₀ G₀ ε : ℝ}
    (hB₀ : 0 < B₀) (hG₀ : 0 < G₀) (hε : 0 < ε)
    (hp : ∀ᶠ k : ℕ in atTop, p k ≤ 64 * primeRectangleRadius k) :
    ∀ᶠ k : ℕ in atTop,
      (p k : ℝ) ^ 2 * (B₀ * (k : ℝ) ^ 2) ^ 5 * (G₀ / (k : ℝ) ^ 40) ≤ ε * (4 : ℝ) ^ k := by
  let K := (64 * 4000 : ℝ) ^ 2 * B₀ ^ 5 * G₀
  filter_upwards [hp, eventually_ge_atTop (1 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K / ε)] with k hpk hk hlarge
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk1
  have hksq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hk1 hk0.le
  have hK : K / (k : ℝ) ^ 2 ≤ ε := by
    apply (div_le_iff₀ (pow_pos hk0 2)).mpr
    calc
      K ≤ (k : ℝ) * ε := (div_le_iff₀ hε).mp hlarge
      _ = ε * (k : ℝ) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hksq hε.le
  have hpk' : (p k : ℝ) ≤ 64 * (primeRectangleRadius k : ℝ) := by exact_mod_cast hpk
  have hB : 0 ≤ (B₀ * (k : ℝ) ^ 2) ^ 5 := pow_nonneg (mul_nonneg hB₀.le (sq_nonneg _)) _
  have hG : 0 ≤ G₀ / (k : ℝ) ^ 40 := div_nonneg hG₀.le (pow_nonneg hk0.le _)
  calc
    _ ≤ (64 * (primeRectangleRadius k : ℝ)) ^ 2 * (B₀ * (k : ℝ) ^ 2) ^ 5 * (G₀ / (k : ℝ) ^ 40) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hpk' 2) hB) hG
    _ = (K / (k : ℝ) ^ 2) * (4 : ℝ) ^ k := radius_replacement_scalar_eq B₀ G₀ hk0
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

end Jsp000881
