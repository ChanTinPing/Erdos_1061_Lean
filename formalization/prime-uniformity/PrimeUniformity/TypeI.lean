module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- A large weighted finite sum forces a contribution from the terms
whose norm reaches the threshold. -/
theorem norm_sum_mul_le_card_threshold {I : Type*} (s : Finset I) (a F : I → ℂ)
    {W M T : ℝ} (hW : 0 ≤ W) (hT : 0 ≤ T)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ W) (hF : ∀ i ∈ s, ‖F i‖ ≤ M) :
    ‖∑ i ∈ s, a i * F i‖ ≤
      W * ((s.card : ℝ) * T + ((s.filter (fun i => T ≤ ‖F i‖)).card : ℝ) * M) := by
  calc
    _ ≤ ∑ i ∈ s, ‖a i * F i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, W * (T + if T ≤ ‖F i‖ then M else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _)).trans ?_
      apply mul_le_mul_of_nonneg_left _ hW
      by_cases ht : T ≤ ‖F i‖
      · rw [if_pos ht]
        exact (hF i hi).trans (le_add_of_nonneg_left hT)
      · simpa only [if_neg ht, add_zero] using (lt_of_not_ge ht).le
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [nsmul_eq_mul]

/-- The unweighted Type I sum along multiples of d inside the interval [L, X]. -/
noncomputable def typeIMultipleSum (L X d : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (X / d), if L ≤ d * m then f (d * m) else 0

/-- Summing along a positive multiplicative fiber agrees with filtering
the original interval by divisibility. -/
theorem typeIMultipleSum_eq_divisibleSum (L X d : ℕ) (hL : 0 < L) (hd : 0 < d)
    (f : ℕ → ℂ) :
    typeIMultipleSum L X d f = ∑ n ∈ (Finset.Icc L X).filter (d ∣ ·), f n := by
  rw [typeIMultipleSum, ← Finset.sum_filter]
  refine Finset.sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
  · intro m hm
    have ⟨hm, hLdm⟩ := Finset.mem_filter.mp hm
    have hdm : d * m ≤ X := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp hm).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hLdm, hdm⟩, ⟨m, rfl⟩⟩
  · intro m _ k _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro n hn
    obtain ⟨hn, k, rfl⟩ := Finset.mem_filter.mp hn
    have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hk : 1 ≤ k := by
      by_cases hz : k = 0
      · subst k
        rw [Nat.mul_zero] at hlo
        omega
      · exact Nat.pos_of_ne_zero hz
    have hkd : k ≤ X / d := (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm])
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hkd⟩, hlo⟩, rfl⟩
  · intro _ _
    rfl

/-- A bounded input gives a bound proportional to the number of multiples. -/
theorem norm_typeIMultipleSum_le (L X d : ℕ) (f : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n, L ≤ n → n ≤ X → ‖f n‖ ≤ B) :
    ‖typeIMultipleSum L X d f‖ ≤ ((X / d : ℕ) : ℝ) * B := by
  unfold typeIMultipleSum
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 (X / d), ‖if L ≤ d * m then f (d * m) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ Finset.Icc 1 (X / d), B := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hL : L ≤ d * m
      · rw [if_pos hL]
        have hm' := (Finset.mem_Icc.mp hm).2
        exact hf _ hL ((Nat.mul_le_mul_left d hm').trans (Nat.mul_div_le X d))
      · simpa only [if_neg hL, norm_zero] using hB
    _ = _ := by simp [nsmul_eq_mul, Nat.card_Icc]

/-- Threshold extraction for a block of positive Type I moduli bounded below by D. -/
theorem norm_typeISum_le_card_threshold (s : Finset ℕ) (L X D : ℕ) (hD : 0 < D)
    (a f : ℕ → ℂ) {W B T : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hd : ∀ d ∈ s, D ≤ d) (ha : ∀ d ∈ s, ‖a d‖ ≤ W)
    (hf : ∀ n, L ≤ n → n ≤ X → ‖f n‖ ≤ B) :
    ‖∑ d ∈ s, a d * typeIMultipleSum L X d f‖ ≤
      W * ((s.card : ℝ) * T +
        ((s.filter (fun d => T ≤ ‖typeIMultipleSum L X d f‖)).card : ℝ) *
          ((X : ℝ) / D * B)) := by
  apply norm_sum_mul_le_card_threshold s a (fun d => typeIMultipleSum L X d f) hW hT ha
  intro d hds
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDd : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd d hds
  refine (norm_typeIMultipleSum_le L X d f hB hf).trans ?_
  refine mul_le_mul_of_nonneg_right (Nat.cast_div_le.trans ?_) hB
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD' hDd

private theorem log_sum_successive_differences {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ))) =
      Real.log (b : ℝ) - Real.log (a : ℝ) :=
  Finset.sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hab

/-- The logarithm on [1, X] is a linear combination of prefix indicators. -/
theorem log_nat_eq_prefix_sum {n X : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    Real.log (n : ℝ) =
      Real.log (X : ℝ) - ∑ k ∈ Finset.Ico 1 X,
        if n ≤ k then Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) else 0 := by
  have hset : (Finset.Ico 1 X).filter (n ≤ ·) = Finset.Ico n X := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hset, log_sum_successive_differences hnX]
  ring

/-- The total absolute coefficient in the logarithmic prefix expansion. -/
theorem log_prefix_coeff_l1 (X : ℕ) (hX : 0 < X) :
    |Real.log (X : ℝ)| +
      (∑ k ∈ Finset.Ico 1 X, |Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)|) =
        2 * Real.log (X : ℝ) := by
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hX))
  have hstep (k : ℕ) (hk : k ∈ Finset.Ico 1 X) :
      0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
    have hk' : 0 < k := (Finset.mem_Ico.mp hk).1
    apply sub_nonneg.mpr
    apply Real.log_le_log
    · exact_mod_cast hk'
    · exact_mod_cast Nat.le_succ k
  have hsum :
      (∑ k ∈ Finset.Ico 1 X, |Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)|) =
        ∑ k ∈ Finset.Ico 1 X, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) :=
    Finset.sum_congr rfl fun k hk => abs_of_nonneg (hstep k hk)
  rw [abs_of_nonneg hlogX, hsum, log_sum_successive_differences (Nat.succ_le_of_lt hX)]
  simp [two_mul]

end PrimeUniformity
