module

public import PrimeUniformity.IntervalBounds
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PrimeUniformity

/-- The interval Gowers norm with the average taken over supported cubes. -/
noncomputable def intervalGowersNorm (d X : ℕ) (w : ℤ → ℝ) : ℝ :=
  (intervalCubeSum d X w / intervalCubeSum d X (fun _ => 1)) ^ (((2 ^ d : ℕ) : ℝ)⁻¹)

private theorem intervalMoment_nonneg (d X : ℕ) (w : ℤ → ℝ) :
    0 ≤ intervalCubeSum d.succ X w / intervalCubeSum d.succ X (fun _ => 1) := by
  apply div_nonneg (intervalCubeSum_succ_nonneg d X w)
  rw [intervalCubeSum_one_eq_card]
  positivity

/-- At positive order, raising the norm to the cube power recovers the normalized moment. -/
theorem intervalGowersNorm_pow (d X : ℕ) (w : ℤ → ℝ) :
    intervalGowersNorm d.succ X w ^ (2 ^ d.succ : ℕ) =
      intervalCubeSum d.succ X w / intervalCubeSum d.succ X (fun _ => 1) := by
  unfold intervalGowersNorm
  rw [← Real.rpow_mul_natCast (intervalMoment_nonneg d X w), inv_mul_cancel₀ (by positivity),
    Real.rpow_one]

/-- Scaling to a one-bounded weight changes its interval norm linearly. -/
theorem intervalGowersNorm_mul_const (d X : ℕ) (a : ℝ) (ha : 0 ≤ a) (w : ℤ → ℝ) :
    intervalGowersNorm d.succ X (fun n => a * w n) = a * intervalGowersNorm d.succ X w := by
  unfold intervalGowersNorm
  rw [intervalCubeSum_mul_const, mul_div_assoc,
    Real.mul_rpow (pow_nonneg ha _) (intervalMoment_nonneg d X w), ← Real.rpow_natCast_mul ha,
    mul_inv_cancel₀ (by positivity), Real.rpow_one]

end PrimeUniformity
