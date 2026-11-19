module

public import PrimeUniformity.PrimeCorrelationScale
public import PrimeUniformity.DyadicDilation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

private theorem exp_log_div_four_lt_of_sqrt_sqrt_lt {X n : ℕ}
    (hX : 0 < X) (hn : X.sqrt.sqrt < n) : Real.exp (Real.log (X : ℝ) / 4) < (n : ℝ) := by
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hpow : X < (n ^ 2) ^ 2 := Nat.sqrt_lt'.mp (Nat.sqrt_lt'.mp hn)
  have hpow' : (X : ℝ) < (n : ℝ) ^ 4 := by
    exact_mod_cast (show X < n ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      exact hpow)
  have hlog := Real.log_lt_log hX' hpow'
  rw [Real.log_pow] at hlog
  exact (Real.exp_lt_exp.mpr (by norm_num at hlog; linarith)).trans_eq (Real.exp_log hn')

/-- A large Vaughan block above the fourth-root cutoffs provides the
side lengths and recovery interval required by Type II coefficient recovery. -/
theorem typeII_vaughan_fourth_root_scales {X i j : ℕ} (hX : 1 < X)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1)
    {p t C : ℝ} (hp : max 2 (Real.log (Real.log (X : ℝ))) ≤ p)
    (ht : 21 * p ≤ t) (hscale : C * t + Real.log 4 ≤ Real.log (X : ℝ) / 4)
    (hlarge : (X : ℝ) * Real.exp (-20 * p) <
      ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖) :
    let L : ℕ := 2 ^ (j + 1) - 1
    let X₀ : ℕ := 2 ^ i * 2 ^ j
    0 < L ∧ X₀ ≤ X ∧
      Real.exp (C * t) ≤ (L : ℝ) ∧ Real.exp (C * t) ≤ (X₀ : ℝ) / L ∧
      (X : ℝ) * Real.exp (-t) ≤ (X₀ : ℝ) ∧ (X₀ : ℝ) / L ≤ (2 : ℝ) ^ i ∧
      dyadicFactorBlock X.sqrt.sqrt X i ⊆ dyadicDilationInterval (2 ^ (i + 1) - 1) ∧
      dyadicFactorBlock X.sqrt.sqrt X j ⊆ dyadicDilationInterval L := by
  intro L X₀
  have hX₀ : 0 < X := by omega
  obtain ⟨hvol, hproduct, _⟩ := dense_columns_of_large_prime_typeIIBlock hX A hA F hF hp hlarge
  have hcard := large_prime_typeIIBlock_card_product hX A F hF ((le_max_right _ _).trans hp) hlarge
  have hpos : 0 < ((dyadicFactorBlock X.sqrt.sqrt X i).card : ℝ) *
      ((dyadicFactorBlock X.sqrt.sqrt X j).card : ℝ) :=
    (mul_pos (Nat.cast_pos.mpr hX₀) (Real.exp_pos _)).trans hcard
  obtain ⟨u, hu⟩ := Finset.card_pos.mp
    (Nat.cast_pos.mp (pos_of_mul_pos_left hpos (Nat.cast_nonneg _)))
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (Nat.cast_pos.mp (pos_of_mul_pos_right hpos (Nat.cast_nonneg _)))
  have hi : X.sqrt.sqrt < (2 : ℕ) ^ (i + 1) :=
    (mem_dyadicFactorBlock.mp hu).1.trans (mem_dyadicFactorBlock.mp hu).2.2.2
  have hj : X.sqrt.sqrt < (2 : ℕ) ^ (j + 1) :=
    (mem_dyadicFactorBlock.mp hv).1.trans (mem_dyadicFactorBlock.mp hv).2.2.2
  have hside (a : ℕ) (ha : X.sqrt.sqrt < (2 : ℕ) ^ (a + 1)) :
      Real.exp (C * t) ≤ (2 : ℝ) ^ a / 2 := by
    have h := (Real.exp_le_exp.mpr hscale).trans
      (exp_log_div_four_lt_of_sqrt_sqrt_lt hX₀ ha).le
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    rw [pow_succ] at h
    linarith only [h]
  have hLmin : (2 : ℕ) ^ j ≤ L := by
    have hposj : 0 < (2 : ℕ) ^ j := by positivity
    dsimp only [L]
    rw [pow_succ]
    omega
  have hLpos : 0 < L := (by positivity : 0 < (2 : ℕ) ^ j).trans_le hLmin
  have hLpos' : 0 < (L : ℝ) := Nat.cast_pos.mpr hLpos
  have hLmin' : (2 : ℝ) ^ j ≤ (L : ℝ) := by exact_mod_cast hLmin
  have hLmax' : (L : ℝ) ≤ (2 : ℝ) ^ j * 2 := by
    rw [← pow_succ]
    exact_mod_cast (Nat.sub_le ((2 : ℕ) ^ (j + 1)) 1)
  have hprod : (X₀ : ℝ) = (2 : ℝ) ^ i * (2 : ℝ) ^ j := by
    simp only [X₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hSub (a : ℕ) : dyadicFactorBlock X.sqrt.sqrt X a ⊆ dyadicDilationInterval (2 ^ (a + 1) - 1) := by
    rw [dyadicDilationInterval_pow_sub_one]
    exact fun _ hn => Finset.mem_Ico.mpr (mem_dyadicFactorBlock.mp hn).2.2
  refine ⟨hLpos, hproduct, ?_, ?_, ?_, ?_, hSub i, hSub j⟩
  · have hhalf : (2 : ℝ) ^ j / 2 ≤ (2 : ℝ) ^ j := by
      linarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
    exact (hside j hj).trans (hhalf.trans hLmin')
  · apply (le_div_iff₀ hLpos').mpr
    calc
      _ ≤ ((2 : ℝ) ^ i / 2) * (L : ℝ) := mul_le_mul_of_nonneg_right (hside i hi) hLpos'.le
      _ ≤ ((2 : ℝ) ^ i / 2) * ((2 : ℝ) ^ j * 2) := mul_le_mul_of_nonneg_left hLmax' (by positivity)
      _ = (X₀ : ℝ) := by rw [hprod]; ring
  · calc
      _ ≤ (X : ℝ) * Real.exp (-21 * p) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [ht])) (Nat.cast_nonneg _)
      _ ≤ _ := by rw [hprod]; exact hvol.le
  · apply (div_le_iff₀ hLpos').mpr
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hLmin' (by positivity)

end PrimeUniformity
