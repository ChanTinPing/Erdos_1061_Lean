module

public import PrimeUniformity.CramerCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter

/-- The exponent of the first dyadic power strictly above the Cramér cutoff. -/
noncomputable def cramerCutoffDyadicIndex (X : ℕ) : ℕ :=
  Nat.log 2 (primeUniformityCutoff X) + 1

/-- The exponent of the first dyadic power strictly above the interval length. -/
def cramerIntervalDyadicIndex (X : ℕ) : ℕ := Nat.log 2 X + 1

theorem cutoff_le_two_pow_cramerCutoffDyadicIndex (X : ℕ) :
    primeUniformityCutoff X ≤ 2 ^ cramerCutoffDyadicIndex X :=
  (Nat.lt_pow_succ_log_self (by decide) _).le

theorem interval_le_two_pow_cramerIntervalDyadicIndex (X : ℕ) :
    X ≤ 2 ^ cramerIntervalDyadicIndex X :=
  (Nat.lt_pow_succ_log_self (by decide) _).le

theorem two_pow_cramerIntervalDyadicIndex_le {X : ℕ} (hX : 0 < X) :
    2 ^ cramerIntervalDyadicIndex X ≤ 2 * X := by
  rw [cramerIntervalDyadicIndex, pow_succ']
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ hX.ne')

private theorem exp_log_rpow_le_cutoff_dyadic_power (X : ℕ) :
    Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)) ≤ (2 : ℝ) ^ cramerCutoffDyadicIndex X := by
  have hfloor : Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)) <
      (primeUniformityCutoff X : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : primeUniformityCutoff X + 1 ≤ 2 ^ cramerCutoffDyadicIndex X :=
    Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
  exact hfloor.le.trans (by exact_mod_cast hpow)

theorem half_pow_cramerCutoffDyadicIndex_le (X : ℕ) :
    (1 / 2 : ℝ) ^ cramerCutoffDyadicIndex X ≤ Real.exp (-(Real.log (X : ℝ) ^ (1 / 10 : ℝ))) := by
  rw [div_pow, one_pow, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (exp_log_rpow_le_cutoff_dyadic_power X)

private theorem eventually_cramerCutoffDyadicIndex_ge (M : ℕ) :
    ∀ᶠ X : ℕ in atTop, M ≤ cramerCutoffDyadicIndex X := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun X : ℕ => Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ht
  filter_upwards [he.eventually_ge_atTop ((2 : ℝ) ^ M)] with X hX
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    (hX.trans (exp_log_rpow_le_cutoff_dyadic_power X))

theorem eventually_cramerCutoffDyadicIndex_pow_four_le :
    ∀ᶠ X : ℕ in atTop, cramerCutoffDyadicIndex X ^ 4 ≤ cramerIntervalDyadicIndex X := by
  let C : ℝ := 1 / Real.log 2 + 1
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (3 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp ht
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop 1,
    hlarge.eventually_ge_atTop (C ^ 4 * Real.log 2)] with X hX hL hscale
  let L := Real.log (X : ℝ)
  let T := L ^ (1 / 10 : ℝ)
  let Q := primeUniformityCutoff X
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hT : 1 ≤ T := Real.one_le_rpow hL (by norm_num)
  have hQpos : 0 < Q := by
    have hQ₁ : 1 ≤ Q := by
      dsimp [Q, primeUniformityCutoff]
      apply Nat.le_floor
      simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (zero_le_one.trans hT)
    exact Nat.zero_lt_one.trans_le hQ₁
  have hQlog : Real.log (Q : ℝ) ≤ T := by
    have hQle : (Q : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos _).le
    simpa only [Real.log_exp] using Real.log_le_log (by exact_mod_cast hQpos) hQle
  have hpow : (2 : ℝ) ^ Nat.log 2 Q ≤ (Q : ℝ) :=
    by exact_mod_cast Nat.pow_log_le_self 2 hQpos.ne'
  have hbin := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hbin
  have hN : (cramerCutoffDyadicIndex X : ℝ) ≤ C * T := by
    change ((Nat.log 2 Q + 1 : ℕ) : ℝ) ≤ C * T
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ T / Real.log 2 + 1 := add_le_add ((le_div_iff₀ hlog₂).mpr (hbin.trans hQlog)) le_rfl
      _ ≤ T / Real.log 2 + T := add_le_add le_rfl hT
      _ = _ := by dsimp [C]; ring
  have hTfour : T ^ (4 : ℕ) = L ^ (2 / 5 : ℝ) := by
    dsimp only [T]
    rw [← Real.rpow_mul_natCast hLpos.le,
      show (1 / 10 : ℝ) * ((4 : ℕ) : ℝ) = 2 / 5 by norm_num]
  have hfour : (cramerCutoffDyadicIndex X : ℝ) ^ (4 : ℕ) * Real.log 2 ≤ L := by
    calc
      _ ≤ (C * T) ^ (4 : ℕ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _) hlog₂.le
      _ = (C ^ (4 : ℕ) * Real.log 2) * L ^ (2 / 5 : ℝ) := by rw [mul_pow, hTfour]; ring
      _ ≤ L ^ (3 / 5 : ℝ) * L ^ (2 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hLpos.le _)
      _ = _ := by
        rw [← Real.rpow_add hLpos, show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num, Real.rpow_one]
  have hxpos : 0 < (X : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hX
  have hcast : (X : ℝ) ≤ (2 : ℝ) ^ cramerIntervalDyadicIndex X :=
    by exact_mod_cast interval_le_two_pow_cramerIntervalDyadicIndex X
  have hk := Real.log_le_log hxpos hcast
  rw [Real.log_pow] at hk
  exact_mod_cast le_of_mul_le_mul_right (hfour.trans hk) hlog₂

/-- The analytic cutoff and interval length satisfy the finite dyadic sieve scales. -/
theorem eventually_cramerCutoff_dyadic_scale :
    ∀ᶠ X : ℕ in atTop,
      primeUniformityCutoff X ≤ 2 ^ cramerCutoffDyadicIndex X ∧
      X ≤ 2 ^ cramerIntervalDyadicIndex X ∧
      2 ^ cramerIntervalDyadicIndex X ≤ 2 * X ∧
      4000 ≤ cramerCutoffDyadicIndex X ∧
      cramerCutoffDyadicIndex X ^ 4 ≤ cramerIntervalDyadicIndex X ∧
      (1 / 2 : ℝ) ^ cramerCutoffDyadicIndex X ≤
        2 * Real.exp (-(Real.log (X : ℝ) ^ (1 / 10 : ℝ))) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_cramerCutoffDyadicIndex_ge 4000,
    eventually_cramerCutoffDyadicIndex_pow_four_le] with X hX hN hfour
  refine ⟨cutoff_le_two_pow_cramerCutoffDyadicIndex X, interval_le_two_pow_cramerIntervalDyadicIndex X,
    two_pow_cramerIntervalDyadicIndex_le (Nat.zero_lt_one.trans_le hX), hN, hfour, ?_⟩
  exact (half_pow_cramerCutoffDyadicIndex_le X).trans (by
    linarith [Real.exp_pos (-(Real.log (X : ℝ) ^ (1 / 10 : ℝ)))])

end PrimeUniformity
