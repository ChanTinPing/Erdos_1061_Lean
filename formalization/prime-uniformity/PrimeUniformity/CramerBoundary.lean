module

public import PrimeUniformity.IntervalBounds
public import PrimeUniformity.IntervalSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

private theorem cramerPrimeSet_at_prime {p : ℕ} (hp : p.Prime) :
    cramerPrimeSet p = insert p (cramerPrimeSet (p - 1)) := by
  classical
  have hp₀ := hp.pos
  ext q
  simp only [cramerPrimeSet, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hq, hprime⟩
    by_cases he : q = p
    · exact Or.inl he
    · exact Or.inr ⟨by omega, hprime⟩
  · rintro (rfl | ⟨hq, hprime⟩)
    · exact ⟨Nat.lt_succ_self _, hp⟩
    · exact ⟨by omega, hprime⟩

private theorem one_lt_real_of_prime {p : ℕ} (hp : p.Prime) : 1 < (p : ℝ) := by
  exact_mod_cast hp.one_lt

theorem cramerNormalization_at_prime {p : ℕ} (hp : p.Prime) :
    cramerNormalization p = ((p : ℝ) / ((p : ℝ) - 1)) * cramerNormalization (p - 1) := by
  classical
  have hp₀ := hp.pos
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀.ne'
  have hnot : p ∉ cramerPrimeSet (p - 1) := by
    simp only [cramerPrimeSet, Finset.mem_filter, Finset.mem_range]
    omega
  unfold cramerNormalization
  rw [cramerPrimeSet_at_prime hp, Finset.prod_insert hnot]
  have he : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by
    field_simp [hp']
  rw [he, inv_div]

theorem cramerWeight_at_prime {p : ℕ} (hp : p.Prime) (n : ℤ) :
    cramerWeight p n = if (p : ℤ) ∣ n then 0
      else ((p : ℝ) / ((p : ℝ) - 1)) * cramerWeight (p - 1) n := by
  classical
  unfold cramerWeight
  simp only [cramerPrimeSet_at_prime hp, cramerNormalization_at_prime hp, Finset.forall_mem_insert]
  by_cases hd : (p : ℤ) ∣ n
  · simp [hd]
  · by_cases hgood : ∀ q ∈ cramerPrimeSet (p - 1), ¬(q : ℤ) ∣ n <;> simp [hd, hgood]

/-- The part of the change at a prime cutoff supported on its multiples. -/
noncomputable def cramerPrimeSparseError (p : ℕ) (n : ℤ) : ℝ :=
  if (p : ℤ) ∣ n then ((p : ℝ) / ((p : ℝ) - 1)) * cramerWeight (p - 1) n else 0

/-- Adding the boundary prime changes the global normalization and deletes its multiples. -/
theorem cramerWeight_previous_sub_at_prime {p : ℕ} (hp : p.Prime) (n : ℤ) :
    cramerWeight (p - 1) n - cramerWeight p n =
      -(cramerWeight (p - 1) n / ((p : ℝ) - 1)) + cramerPrimeSparseError p n := by
  have hp₁ : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (one_lt_real_of_prime hp)).ne'
  rw [cramerWeight_at_prime hp]
  by_cases hd : (p : ℤ) ∣ n
  · simp only [hd, if_true, cramerPrimeSparseError, sub_zero]
    field_simp [hp₁]
    ring
  · simp only [hd, if_false, cramerPrimeSparseError, add_zero]
    field_simp [hp₁]
    ring

/-- One-based interval endpoints divisible by the given modulus. -/
def intervalMultipleEndpoints (X p : ℕ) : Finset (Fin X) :=
  Finset.univ.filter fun i => p ∣ i.val + 1

private theorem intervalEndpoint_divisible {X p : ℕ} (i : Fin X) :
    ((p : ℤ) ∣ intervalEndpoint i) ↔ p ∣ i.val + 1 := by
  rw [show intervalEndpoint i = ((i.val + 1 : ℕ) : ℤ) by simp [intervalEndpoint]]
  exact Int.natCast_dvd_natCast

/-- The count of positive multiples at most X is bounded by X / p. -/
theorem card_intervalMultipleEndpoints_le (X p : ℕ) (hp : 0 < p) :
    (intervalMultipleEndpoints X p).card ≤ X / p := by
  classical
  have hdiv (i : Fin X) (hi : i ∈ intervalMultipleEndpoints X p) : p ∣ i.val + 1 := by
    simpa [intervalMultipleEndpoints] using hi
  have hpos (i : Fin X) (hi : i ∈ intervalMultipleEndpoints X p) :
      1 ≤ (i.val + 1) / p :=
    (Nat.le_div_iff_mul_le hp).mpr (by
      simpa only [one_mul] using Nat.le_of_dvd (Nat.succ_pos _) (hdiv i hi))
  have hcount : (intervalMultipleEndpoints X p).card ≤ (Finset.range (X / p)).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin X => (i.val + 1) / p - 1)
    · intro i hi
      apply Finset.mem_range.mpr
      change (i.val + 1) / p - 1 < X / p
      have hup : (i.val + 1) / p ≤ X / p := Nat.div_le_div_right i.isLt
      have hlo := hpos i hi
      omega
    · intro i hi j hj hij
      change (i.val + 1) / p - 1 = (j.val + 1) / p - 1 at hij
      have heq : (i.val + 1) / p = (j.val + 1) / p := by
        have hii := hpos i hi
        have hjj := hpos j hj
        omega
      have hval : i.val + 1 = j.val + 1 := by
        simpa only [Nat.div_mul_cancel (hdiv i hi), Nat.div_mul_cancel (hdiv j hj)]
          using congrArg (fun k : ℕ => k * p) heq
      exact Fin.ext (Nat.add_right_cancel hval)
  simpa only [Finset.card_range] using hcount

private theorem intervalCubeSum_cramerBoundary_uniform_le
    (d X p : ℕ) (hp : p.Prime) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |cramerWeight (p - 1) n| ≤ B) :
    intervalCubeSum d X (fun n => -(cramerWeight (p - 1) n / ((p : ℝ) - 1))) ≤
      (X : ℝ) ^ (d + 1) * (B / ((p : ℝ) - 1)) ^ (2 ^ d : ℕ) := by
  have hp₁ : 0 < (p : ℝ) - 1 := sub_pos.mpr (one_lt_real_of_prime hp)
  have hB' := div_nonneg hB hp₁.le
  have h := intervalCubeSum_le_support d X
    (fun n => -(cramerWeight (p - 1) n / ((p : ℝ) - 1))) Finset.univ hB'
    (by
      intro n
      by_cases hn : 1 ≤ n ∧ n ≤ (X : ℤ)
      · simp only [intervalWeight, if_pos hn, Complex.norm_real, Real.norm_eq_abs,
          abs_neg, abs_div, abs_of_pos hp₁]
        exact div_le_div_of_nonneg_right (hweight n hn.1 hn.2) hp₁.le
      · simpa only [intervalWeight, if_neg hn, norm_zero] using hB')
    (fun i hi => (hi (Finset.mem_univ i)).elim)
  simpa only [Finset.card_univ, Fintype.card_fin, pow_succ'] using h

private theorem intervalCubeSum_cramerBoundary_sparse_le
    (d X p : ℕ) (hp : p.Prime) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |cramerWeight (p - 1) n| ≤ B) :
    intervalCubeSum d X (cramerPrimeSparseError p) ≤
      ((X / p : ℕ) : ℝ) * (X : ℝ) ^ d * (2 * B) ^ (2 ^ d : ℕ) := by
  have hp₁ : 0 < (p : ℝ) - 1 := sub_pos.mpr (one_lt_real_of_prime hp)
  have h₂ : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hk₂ : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ hp₁).mpr
    linarith
  have hk₀ : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hp₁.le
  have hB' : 0 ≤ 2 * B := mul_nonneg (by norm_num) hB
  refine (intervalCubeSum_le_support d X (cramerPrimeSparseError p)
    (intervalMultipleEndpoints X p) hB' ?_ ?_).trans ?_
  · intro n
    by_cases hn : 1 ≤ n ∧ n ≤ (X : ℤ)
    · by_cases hd : (p : ℤ) ∣ n
      · simp only [intervalWeight, if_pos hn, cramerPrimeSparseError, if_pos hd,
          Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk₀]
        exact mul_le_mul hk₂ (hweight n hn.1 hn.2) (abs_nonneg _) (by norm_num)
      · simpa only [intervalWeight, if_pos hn, cramerPrimeSparseError, if_neg hd,
          Complex.ofReal_zero, norm_zero] using hB'
    · simpa only [intervalWeight, if_neg hn, norm_zero] using hB'
  · intro i hi
    have hd : ¬(p : ℤ) ∣ intervalEndpoint i := by
      intro hd
      exact hi (by simpa [intervalMultipleEndpoints] using (intervalEndpoint_divisible i).mp hd)
    simp [intervalWeight, cramerPrimeSparseError, hd]
  · have hcard : ((intervalMultipleEndpoints X p).card : ℝ) ≤ ((X / p : ℕ) : ℝ) := by
      exact_mod_cast card_intervalMultipleEndpoints_le X p hp.pos
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hB' _)

/-- The interval cube moment of the change at a prime cutoff. The first term
comes from the normalization change and the second from the deleted multiples. -/
theorem exists_intervalCubeSum_cramerBoundary_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X p : ℕ), p.Prime → ∀ (B : ℝ), 0 ≤ B →
      (∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |cramerWeight (p - 1) n| ≤ B) →
      |intervalCubeSum d.succ X (fun n => cramerWeight (p - 1) n - cramerWeight p n)| ≤
        C * ((X : ℝ) ^ (d.succ + 1) * (B / ((p : ℝ) - 1)) ^ (2 ^ d.succ : ℕ) +
          ((X / p : ℕ) : ℝ) * (X : ℝ) ^ d.succ * (2 * B) ^ (2 ^ d.succ : ℕ)) := by
  obtain ⟨C, hC, hadd⟩ := exists_intervalCubeSum_succ_add_le d
  refine ⟨C, hC, ?_⟩
  intro X p hp B hB hweight
  rw [abs_of_nonneg (intervalCubeSum_succ_nonneg d X _)]
  simp_rw [cramerWeight_previous_sub_at_prime hp]
  refine (hadd X (fun n => -(cramerWeight (p - 1) n / ((p : ℝ) - 1)))
    (cramerPrimeSparseError p)).trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add
    (intervalCubeSum_cramerBoundary_uniform_le d.succ X p hp hB hweight)
    (intervalCubeSum_cramerBoundary_sparse_le d.succ X p hp hB hweight)) hC.le

end PrimeUniformity
