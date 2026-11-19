module

public import Jsp000881.Coefficients
import all Jsp000881.Coefficients
public import Jsp000881.PrimeWeights
import all Jsp000881.PrimeWeights

public section

namespace Jsp000881

open Filter

/-- A common positive radius containing the lattice coordinates and all six
prime-form values at the dyadic scale. -/
def primeRectangleRadius (k : ℕ) : ℕ := 4000 * k ^ 14 * 2 ^ k

theorem primeRectangleRadius_cast {R : Type*} [Semiring R] (k : ℕ) :
    (primeRectangleRadius k : R) = 4000 * (k : R) ^ 14 * (2 : R) ^ k := by
  simp only [primeRectangleRadius, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem primeRectangleRadius_int_eq (k : ℕ) :
    (primeRectangleRadius k : ℤ) = 4000 * (k : ℤ) ^ 7 * (k : ℤ) ^ 7 * (2 : ℤ) ^ k := by
  rw [primeRectangleRadius_cast]
  ring

theorem primeRectangleRadius_pos {k : ℕ} (hk : 1 ≤ k) : 0 < primeRectangleRadius k := by
  have hk0 : 0 < k := hk
  unfold primeRectangleRadius
  positivity

theorem dyadicHeight_le_primeRectangleRadius {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ) ^ k ≤ (primeRectangleRadius k : ℤ) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hcoef : (1 : ℤ) ≤ 4000 * (k : ℤ) ^ 14 :=
    one_le_mul_of_one_le_of_one_le (by decide) (one_le_pow₀ hk')
  rw [primeRectangleRadius_cast]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef
    (show (0 : ℤ) ≤ (2 : ℤ) ^ k by positivity)

theorem primeRectangleRadius_tendsto : Tendsto primeRectangleRadius atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have h : (2 : ℕ) ^ k ≤ primeRectangleRadius k := by
    exact_mod_cast dyadicHeight_le_primeRectangleRadius hk
  exact k.lt_two_pow_self.le.trans h

theorem log_primeRectangleRadius_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (primeRectangleRadius k : ℝ) ≤ 5000 * (k : ℝ) := by
  rw [primeRectangleRadius_cast]
  exact log_scale_upper (by exact_mod_cast hk)

theorem dyadic_log_le_log_primeRectangleRadius {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * Real.log 2 ≤ Real.log (primeRectangleRadius k : ℝ) := by
  have h : (2 : ℝ) ^ k ≤ (primeRectangleRadius k : ℝ) := by
    exact_mod_cast dyadicHeight_le_primeRectangleRadius hk
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num) _) h

theorem rectangle_point_radius {k : ℕ} {θ : PlaneIndex} {nm : ℤ × ℤ}
    (hk : 8 ≤ k) (hθ : ParameterBox θ ((k : ℤ) ^ 7))
    (hnm : nm ∈ latticeRectangle ((2 : ℤ) ^ k)) :
    |nm.1| ≤ (primeRectangleRadius k : ℤ) ∧ |nm.2| ≤ (primeRectangleRadius k : ℤ) ∧
      ∀ i : Fin 6, 1 ≤ (integralRow θ i).eval nm.1 nm.2 ∧
        (integralRow θ i).eval nm.1 nm.2 ≤ (primeRectangleRadius k : ℤ) := by
  have hkz : (8 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hz : (100 : ℤ) ≤ (k : ℤ) ^ 7 :=
    (by decide : (100 : ℤ) ≤ (8 : ℤ) ^ 7).trans (pow_le_pow_left₀ (by decide) hkz 7)
  have hT : (8 : ℤ) ≤ (2 : ℤ) ^ k := by
    exact_mod_cast (show (8 : ℕ) ≤ (2 : ℕ) ^ k from hk.trans k.lt_two_pow_self.le)
  have hR := dyadicHeight_le_primeRectangleRadius ((by decide : (1 : ℕ) ≤ 8).trans hk)
  obtain ⟨h₁, h₂⟩ := latticeRectangle_subset_square hT hnm
  have hgeom := rectangle_heights hz (by omega) hθ ((mem_latticeRectangle (by omega)).mp hnm)
  refine ⟨h₁.trans hR, h₂.trans hR, fun i => ?_⟩
  rw [integralRow_eval]
  exact ⟨(by decide : (1 : ℤ) ≤ 127).trans (hgeom.coordinate_large i).le,
    (hgeom.coordinate_upper i).trans_eq (primeRectangleRadius_int_eq k).symm⟩

theorem eventually_rectangle_point_radius :
    ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex, ParameterBox θ ((k : ℤ) ^ 7) →
      ∀ nm ∈ latticeRectangle ((2 : ℤ) ^ k),
        |nm.1| ≤ (primeRectangleRadius k : ℤ) ∧ |nm.2| ≤ (primeRectangleRadius k : ℤ) ∧
          ∀ i : Fin 6, 1 ≤ (integralRow θ i).eval nm.1 nm.2 ∧
            (integralRow θ i).eval nm.1 nm.2 ≤ (primeRectangleRadius k : ℤ) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with k hk
  exact fun _ hθ _ hnm => rectangle_point_radius hk hθ hnm

end Jsp000881
