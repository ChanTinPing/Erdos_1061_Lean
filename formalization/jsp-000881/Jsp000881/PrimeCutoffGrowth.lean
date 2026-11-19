module

public import Jsp000881.CramerDecay
import all Jsp000881.CramerDecay
public import Jsp000881.PrimeInput
import all Jsp000881.PrimeInput
public import Jsp000881.RectangleRadius
import all Jsp000881.RectangleRadius
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Growth of the analytic Cramér cutoff

The analytic cutoff is bounded by a dyadic power whose exponent tends to
infinity and whose fourth power is eventually smaller than the scale
index. This matches the elementary model estimate.
-/

public section

namespace Jsp000881

open Filter

noncomputable def primeCutoffDyadicIndex (k : ℕ) : ℕ :=
  ⌈(k : ℝ) ^ (1 / 8 : ℝ)⌉₊

private theorem eventually_realPower_nat_ge {r : ℝ} (hr : 0 < r) (b : ℝ) :
    ∀ᶠ k : ℕ in atTop, b ≤ (k : ℝ) ^ r :=
  ((tendsto_rpow_atTop hr).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop b

theorem tendsto_primeCutoffDyadicIndex : Tendsto primeCutoffDyadicIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_realPower_nat_ge (by norm_num : 0 < (1 / 8 : ℝ)) (B : ℝ)] with k hk
  have hceil : (k : ℝ) ^ (1 / 8 : ℝ) ≤ (primeCutoffDyadicIndex k : ℝ) := Nat.le_ceil _
  exact_mod_cast hk.trans hceil

private theorem eventually_primeCutoffDyadicIndex_fourth_le :
    ∀ᶠ k : ℕ in atTop, primeCutoffDyadicIndex k ^ 4 ≤ k := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_realPower_nat_ge (by norm_num : 0 < (1 / 2 : ℝ)) 16] with k hk hlarge
  let r := (k : ℝ) ^ (1 / 8 : ℝ)
  let t := (k : ℝ) ^ (1 / 2 : ℝ)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk1
  have hr1 : 1 ≤ r := Real.one_le_rpow hk1 (by norm_num)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hk0.le _
  have hceil : (primeCutoffDyadicIndex k : ℝ) < r + 1 :=
    Nat.ceil_lt_add_one (zero_le_one.trans hr1)
  have hceil' : (primeCutoffDyadicIndex k : ℝ) ≤ 2 * r := by linarith only [hceil, hr1]
  have hrt : r ^ 4 = t := by
    dsimp only [r, t]
    rw [← Real.rpow_mul_natCast hk0.le,
      show (1 / 8 : ℝ) * ((4 : ℕ) : ℝ) = 1 / 2 by norm_num]
  have htt : t * t = (k : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_add hk0, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hpow : (primeCutoffDyadicIndex k : ℝ) ^ 4 ≤ (k : ℝ) := by
    calc
      _ ≤ (2 * r) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil' 4
      _ = 16 * t := by rw [mul_pow, hrt]; norm_num
      _ ≤ t * t := mul_le_mul_of_nonneg_right hlarge ht0
      _ = _ := htt
  exact_mod_cast hpow

/-- The exact analytic cutoff has the growth required by the finite
Cramér model, for any ambient extent with an eventual log-linear bound. -/
theorem eventually_primeUniformityCutoff_dyadic_growth {X : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hX : ∀ᶠ k in atTop, 1 ≤ X k ∧ Real.log (X k : ℝ) ≤ C * (k : ℝ)) :
    ∀ᶠ k in atTop, 1 ≤ primeUniformityCutoff (X k) ∧
      primeUniformityCutoff (X k) ≤ 2 ^ primeCutoffDyadicIndex k ∧ primeCutoffDyadicIndex k ^ 4 ≤ k := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hX, eventually_ge_atTop (1 : ℕ), eventually_primeCutoffDyadicIndex_fourth_le,
    eventually_realPower_nat_ge (by norm_num : 0 < (1 / 40 : ℝ))
      (C ^ (1 / 10 : ℝ) / Real.log 2)] with k hx hk hfour hlarge
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk1
  have hx1 : (1 : ℝ) ≤ (X k : ℝ) := by exact_mod_cast hx.1
  have hxlog : 0 ≤ Real.log (X k : ℝ) := Real.log_nonneg hx1
  have hscale : C ^ (1 / 10 : ℝ) ≤ Real.log 2 * (k : ℝ) ^ (1 / 40 : ℝ) := by
    calc
      _ ≤ (k : ℝ) ^ (1 / 40 : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).mp hlarge
      _ = _ := mul_comm _ _
  have hupper : Real.log (X k : ℝ) ^ (1 / 10 : ℝ) ≤
      (primeCutoffDyadicIndex k : ℝ) * Real.log 2 := by
    calc
      _ ≤ (C * (k : ℝ)) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow hxlog hx.2 (by norm_num)
      _ = C ^ (1 / 10 : ℝ) * (k : ℝ) ^ (1 / 10 : ℝ) := Real.mul_rpow hC.le hk0.le
      _ ≤ (Real.log 2 * (k : ℝ) ^ (1 / 40 : ℝ)) * (k : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hk0.le _)
      _ = (k : ℝ) ^ (1 / 8 : ℝ) * Real.log 2 := by
        rw [mul_assoc, ← Real.rpow_add hk0, show (1 / 40 : ℝ) + 1 / 10 = 1 / 8 by norm_num]
        exact mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog2.le
  have hexp : Real.exp (Real.log (X k : ℝ) ^ (1 / 10 : ℝ)) ≤ (2 : ℝ) ^ primeCutoffDyadicIndex k := by
    have h := Real.exp_le_exp.mpr hupper
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  refine ⟨?_, ?_, hfour⟩
  · unfold primeUniformityCutoff
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (Real.rpow_nonneg hxlog (1 / 10))
  · unfold primeUniformityCutoff
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hexp

theorem uniformCramerMassLowerBound_of_primeUniformityCutoff {X : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hX : ∀ᶠ k in atTop, 1 ≤ X k ∧ Real.log (X k : ℝ) ≤ C * (k : ℝ)) :
    UniformCramerMassLowerBound (fun k => primeUniformityCutoff (X k)) :=
  uniformCramerMassLowerBound_of_dyadic_growth _ primeCutoffDyadicIndex
    tendsto_primeCutoffDyadicIndex (eventually_primeUniformityCutoff_dyadic_growth hC hX)

theorem uniformCramerMassLowerBound_at_rectangleRadius :
    UniformCramerMassLowerBound (fun k => primeUniformityCutoff (primeRectangleRadius k)) := by
  apply uniformCramerMassLowerBound_of_primeUniformityCutoff (show (0 : ℝ) < 5000 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact ⟨primeRectangleRadius_pos hk, log_primeRectangleRadius_le hk⟩

end Jsp000881
