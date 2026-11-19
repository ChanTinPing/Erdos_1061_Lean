module

public import PrimeUniformity.CramerNormalization
public import PrimeUniformity.LogSavings
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter

/-- The cutoff used when the prime bound is strict, as in Leng's Cramér model. -/
noncomputable def strictPrimeUniformityCutoff (X : ℕ) : ℕ :=
  ⌈Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ))⌉₊ - 1

theorem strictPrimeUniformityCutoff_le (X : ℕ) :
    strictPrimeUniformityCutoff X ≤ primeUniformityCutoff X := by
  unfold strictPrimeUniformityCutoff primeUniformityCutoff
  have h := Nat.ceil_le_floor_add_one (Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)))
  omega

/-- A prime at the endpoint is the only possible discrepancy between the
strict cutoff and the closed cutoff. -/
theorem strictPrimeUniformityCutoff_cases (X : ℕ) :
    strictPrimeUniformityCutoff X = primeUniformityCutoff X ∨
      (strictPrimeUniformityCutoff X = primeUniformityCutoff X - 1 ∧
        (primeUniformityCutoff X : ℝ) = Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ))) := by
  let T := Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ))
  let Q := primeUniformityCutoff X
  have hQ : (Q : ℝ) ≤ T := Nat.floor_le (Real.exp_pos _).le
  by_cases he : (Q : ℝ) = T
  · right
    refine ⟨?_, he⟩
    change ⌈T⌉₊ - 1 = Q - 1
    rw [← he, Nat.ceil_natCast]
  · left
    change ⌈T⌉₊ - 1 = Q
    have hceil : ⌈T⌉₊ = Q + 1 := by
      apply (Nat.ceil_eq_iff (by omega : Q + 1 ≠ 0)).mpr
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      exact ⟨lt_of_le_of_ne hQ he, (Nat.lt_floor_add_one T).le⟩
    omega

/-- Below the prime uniformity cutoff the Cramér weight is bounded by
a fixed power of the logarithm of the interval length. -/
theorem eventually_abs_cramerWeight_le_log_pow :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℕ in atTop,
      ∀ Q : ℕ, Q ≤ primeUniformityCutoff X → ∀ n : ℤ,
        |cramerWeight Q n| ≤ B * Real.log (X : ℝ) ^ (8 : ℕ) := by
  let B := Real.exp 5 * (2 * (1 / Real.log 2 + 1)) ^ (8 : ℕ)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 1] with X hX
  intro Q hQ n
  let L := Real.log (X : ℝ)
  let N := Nat.log 2 Q + 1
  have hQpow : Q ≤ (2 : ℕ) ^ N := (Nat.lt_pow_succ_log_self (by decide) Q).le
  have hN : (N : ℝ) ≤ (1 / Real.log 2 + 1) * L := by
    by_cases hQ₀ : Q = 0
    · simp only [N, hQ₀, Nat.log_zero_right, Nat.zero_add, Nat.cast_one]
      exact (by linarith [one_div_pos.mpr hlog₂] : (1 : ℝ) ≤ 1 / Real.log 2 + 1).trans
        (le_mul_of_one_le_right (by positivity) hX)
    · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ₀
      have hpow : (2 : ℝ) ^ Nat.log 2 Q ≤ (Q : ℝ) :=
        by exact_mod_cast Nat.pow_log_le_self 2 hQ₀
      have hlQ := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow] at hlQ
      have hlogQ : Real.log (Q : ℝ) ≤ L := by
        have h₁ : (Q : ℝ) ≤ (primeUniformityCutoff X : ℝ) := by exact_mod_cast hQ
        have h₂ : (primeUniformityCutoff X : ℝ) ≤ Real.exp (L ^ (1 / 10 : ℝ)) :=
          Nat.floor_le (Real.exp_pos _).le
        have h₃ := Real.log_le_log (by exact_mod_cast hQpos) (h₁.trans h₂)
        rw [Real.log_exp] at h₃
        exact h₃.trans (by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hX (show (1 / 10 : ℝ) ≤ 1 by norm_num))
      have hnlog : (Nat.log 2 Q : ℝ) ≤ L / Real.log 2 :=
        (le_div_iff₀ hlog₂).mpr (hlQ.trans hlogQ)
      simp only [N, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ L / Real.log 2 + L := add_le_add hnlog hX
        _ = _ := by ring
  have hmax : max (N : ℝ) 1 ≤ (1 / Real.log 2 + 1) * L :=
    max_le hN ((by linarith [one_div_pos.mpr hlog₂] : (1 : ℝ) ≤ 1 / Real.log 2 + 1).trans
      (le_mul_of_one_le_right (by positivity) hX))
  calc
    _ ≤ Real.exp 5 * (2 * max (N : ℝ) 1) ^ (8 : ℕ) := abs_cramerWeight_le_poly_dyadic hQpow n
    _ ≤ Real.exp 5 * (2 * ((1 / Real.log 2 + 1) * L)) ^ (8 : ℕ) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hmax (by norm_num)) _)
        (Real.exp_pos _).le
    _ = _ := by dsimp [B]; rw [← mul_assoc, mul_pow, mul_assoc]

end PrimeUniformity
