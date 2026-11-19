module

public import PrimeUniformity.CramerNormalization
public import Jsp000881.CramerSieve
public import Jsp000881.ModelTransfer
import all Jsp000881.ModelTransfer
public import Jsp000881.CramerBudget

@[expose] public section

namespace Jsp000881

open Filter
open scoped BigOperators

private theorem cramerPrimeSet_prime {Q p : ℕ} (hp : p ∈ cramerPrimeSet Q) : p.Prime := by
  unfold cramerPrimeSet at hp
  exact (Finset.mem_filter.mp hp).2

theorem cramerNormalization_pos (Q : ℕ) : 0 < cramerNormalization Q := by
  unfold cramerNormalization
  apply Finset.prod_pos
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (cramerPrimeSet_prime hp).pos
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (show 1 < p from (by decide : 1 < 2).trans_le (cramerPrimeSet_prime hp).two_le)
  exact inv_pos.mpr (sub_pos.mpr ((div_lt_iff₀ hp0).mpr (by simpa using hp1)))

export PrimeUniformity (cramerNormalization_le_cutoff)

private theorem normalized_product (Q : ℕ) (θ : PlaneIndex) :
    (cramerNormalization Q) ^ 6 * (∏ p ∈ cramerPrimeSet Q, (1 - localBadDensity θ p)) =
      ∏ p ∈ cramerPrimeSet Q, residueFactor θ p := by
  unfold cramerNormalization
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact p.Prime := ⟨cramerPrimeSet_prime hp⟩
  rw [residueFactor_eq_of_prime, localBadDensity_eq_one_sub_good, sub_sub_cancel, inv_pow]
  simp only [div_eq_mul_inv]
  ac_rfl

private theorem cramerMass_survival (Q : ℕ) (θ : PlaneIndex) (X : Finset (ℤ × ℤ)) :
    (∑ nm ∈ X, ∏ i : Fin 6, cramerWeight Q ((sextupleOn θ nm).coord i)) =
      (cramerNormalization Q) ^ 6 * survivingWeight (cramerPrimeSet Q) X
        (fun p nm => ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ nm).coord i) (fun _ => 1) := by
  classical
  unfold survivingWeight
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro nm _
  by_cases h : ∀ p ∈ cramerPrimeSet Q, ¬ ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ nm).coord i
  · rw [if_pos h, mul_one]
    have hw (i : Fin 6) : cramerWeight Q ((sextupleOn θ nm).coord i) = cramerNormalization Q :=
      if_pos (fun p hp hd => h p hp ⟨i, hd⟩)
    simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hp, i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (if_neg (fun hgood => hgood p hp hi))

noncomputable def cramerBoxBudget (Q : ℕ) (θ : PlaneIndex) (a b : ℤ) (L : ℕ) : ℝ :=
  let A := (a : ℝ) * (b : ℝ)
  (cramerNormalization Q) ^ 6 *
    (A * (∑ J ∈ (cramerPrimeSet Q).powersetCard (L + 1), ∏ p ∈ J, localBadDensity θ p) +
      boxSieveError (cramerPrimeSet Q) a b L)

noncomputable def cramerTruncationBudget (Q : ℕ) (θ : PlaneIndex) (T : ℤ) (L : ℕ) : ℝ :=
  cramerBoxBudget Q θ (rectangleFirstLength T) (rectangleSecondLength T) L

/-- The finite Cramér mass of any integer rectangle has a uniform positive
area coefficient and two explicit truncation errors. -/
theorem cramerMass_ge_box_area_sub_budget :
    ∃ d : ℝ, 0 < d ∧ ∀ (Q : ℕ) (θ : PlaneIndex) (s a t b : ℤ) (L : ℕ),
      Odd L → 0 ≤ a → 0 ≤ b → LocallyAdmissible θ →
      d * (a : ℝ) * (b : ℝ) - cramerBoxBudget Q θ a b L ≤
        ∑ nm ∈ (interval s a).product (interval t b),
          ∏ i : Fin 6, cramerWeight Q ((sextupleOn θ nm).coord i) := by
  obtain ⟨d, hd, hprod⟩ := uniform_residueFactor_product_lower_bound
  refine ⟨d, hd, ?_⟩
  intro Q θ s a t b L hL ha hb hθ
  let P := cramerPrimeSet Q
  let A := (a : ℝ) * (b : ℝ)
  let tail := ∑ J ∈ P.powersetCard (L + 1), ∏ p ∈ J, localBadDensity θ p
  let B := cramerNormalization Q ^ 6
  have hP : ∀ p ∈ P, p.Prime := fun _ => cramerPrimeSet_prime
  have hN : 0 < B := pow_pos (cramerNormalization_pos Q) _
  have hA : 0 ≤ A := mul_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)
  have h₁ := rectangleSieveLowerBound θ P hP s a t b ha hb L hL
  have h₂ := independentTruncation_ge_product_sub_tail P (localBadDensity θ)
    (fun p hp => localBadDensity_bounds θ (hP p hp)) L hL
  have h₃ := mul_le_mul_of_nonneg_left h₂ hA
  have hS := hprod θ P hθ hP
  rw [← normalized_product Q θ] at hS
  have hS' := mul_le_mul_of_nonneg_right hS hA
  rw [cramerMass_survival]
  change d * (a : ℝ) * (b : ℝ) - B * (A * tail + boxSieveError P a b L) ≤ _
  have h₄ := mul_le_mul_of_nonneg_left h₁ hN.le
  have h₅ := mul_le_mul_of_nonneg_left h₃ hN.le
  linarith only [hS', h₄, h₅]

theorem cramerMass_ge_area_sub_budget :
    ∃ d : ℝ, 0 < d ∧ ∀ (Q : ℕ) (θ : PlaneIndex) (T : ℤ) (L : ℕ), Odd L →
      10000000000 ≤ T → LocallyAdmissible θ →
      d * (rectangleFirstLength T : ℝ) * (rectangleSecondLength T : ℝ) -
        cramerTruncationBudget Q θ T L ≤ mixedRectangleMass Q θ T 0 := by
  obtain ⟨d, hd, hmain⟩ := cramerMass_ge_box_area_sub_budget
  refine ⟨d, hd, ?_⟩
  intro Q θ T L hL hT hθ
  have hT₀ : 0 ≤ T := by omega
  have hTr : (0 : ℝ) ≤ T := by exact_mod_cast hT₀
  obtain ⟨ha, _, hb, _⟩ := rectangle_length_bounds hT
  have ha' : 0 ≤ rectangleFirstLength T := by exact_mod_cast ((div_nonneg hTr (by norm_num)).trans ha)
  have hb' : 0 ≤ rectangleSecondLength T := by exact_mod_cast ((div_nonneg hTr (by norm_num)).trans hb)
  simp only [mixedRectangleMass, latticeRectangle_eq_intervals hT₀, Nat.not_lt_zero, if_false]
  exact hmain Q θ (rectangleFirstStart T) _ rectangleSecondStart _ L hL ha' hb' hθ

/-- An explicit scalar estimate for the Cramér sieve error on a rectangle
with two nonnegative side lengths bounded by the same height. -/
theorem cramerBoxBudget_le {Q L : ℕ} (hQ : 1 ≤ Q) (θ : PlaneIndex) {a b T : ℤ}
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha' : a ≤ T) (hb' : b ≤ T) :
    cramerBoxBudget Q θ a b L ≤ (Q : ℝ) ^ 6 *
      ((T : ℝ) ^ 2 * ((∑ p ∈ cramerPrimeSet Q, localBadDensity θ p) ^ (L + 1) /
        ((L + 1).factorial : ℝ)) + 2 * (T : ℝ) * ((Q ^ L : ℕ) : ℝ) ^ 2 +
        ((Q ^ L : ℕ) : ℝ) ^ 3) := by
  let P := cramerPrimeSet Q
  let F := ((∑ p ∈ P, localBadDensity θ p) ^ (L + 1)) / ((L + 1).factorial : ℝ)
  let D : ℝ := (Q ^ L : ℕ)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Q := by
    have hp' := Finset.mem_filter.mp hp
    exact ⟨hp'.2, Nat.lt_succ_iff.mp (Finset.mem_range.mp hp'.1)⟩
  have hnonneg (p : ℕ) (hp : p ∈ P) : 0 ≤ localBadDensity θ p :=
    (localBadDensity_bounds θ (hP p hp).1).1
  have hT₀ : (0 : ℝ) ≤ T := by exact_mod_cast ha₀.trans ha'
  have haR : (a : ℝ) ≤ T := by exact_mod_cast ha'
  have hbR : (b : ℝ) ≤ T := by exact_mod_cast hb'
  have hb₀R : (0 : ℝ) ≤ b := by exact_mod_cast hb₀
  have hA : (a : ℝ) * (b : ℝ) ≤ (T : ℝ) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul haR hbR hb₀R hT₀
  have hF : 0 ≤ F :=
    div_nonneg (pow_nonneg (Finset.sum_nonneg hnonneg) _) (Nat.cast_nonneg _)
  have htail := sum_powersetCard_prod_le_pow_div_factorial P (localBadDensity θ) hnonneg (L + 1)
  have hfirst := mul_le_mul hA htail
    (Finset.sum_nonneg fun J hJ => Finset.prod_nonneg fun p hp =>
      hnonneg p ((Finset.mem_powersetCard.mp hJ).1 hp)) (sq_nonneg (T : ℝ))
  have hbox := boxSieveError_le hQ hP ha₀ hb₀ (L := L)
  have hsum : (a : ℝ) + (b : ℝ) ≤ 2 * (T : ℝ) := by linarith only [haR, hbR]
  have hbox' : boxSieveError P a b L ≤ 2 * (T : ℝ) * D ^ 2 + D ^ 3 :=
    hbox.trans (add_le_add (mul_le_mul_of_nonneg_right hsum (sq_nonneg D)) le_rfl)
  have hN := pow_le_pow_left₀ (cramerNormalization_pos Q).le (cramerNormalization_le_cutoff hQ) 6
  have hE : 0 ≤ (T : ℝ) ^ 2 * F + (2 * (T : ℝ) * D ^ 2 + D ^ 3) := by
    have hD : 0 ≤ D := Nat.cast_nonneg _
    positivity
  unfold cramerBoxBudget
  calc
    _ ≤ (Q : ℝ) ^ 6 * ((T : ℝ) ^ 2 * F + (2 * (T : ℝ) * D ^ 2 + D ^ 3)) :=
      (mul_le_mul_of_nonneg_left (add_le_add hfirst hbox') (pow_nonneg (cramerNormalization_pos Q).le 6)).trans
        (mul_le_mul_of_nonneg_right hN hE)
    _ = _ := by dsimp [F, D, P]; rw [add_assoc]

theorem cramerTruncationBudget_le {Q L : ℕ} (hQ : 1 ≤ Q) (θ : PlaneIndex) {T : ℤ}
    (hT : 10000000000 ≤ T) :
    cramerTruncationBudget Q θ T L ≤ (Q : ℝ) ^ 6 *
      ((T : ℝ) ^ 2 * ((∑ p ∈ cramerPrimeSet Q, localBadDensity θ p) ^ (L + 1) /
        ((L + 1).factorial : ℝ)) + 2 * (T : ℝ) * ((Q ^ L : ℕ) : ℝ) ^ 2 +
        ((Q ^ L : ℕ) : ℝ) ^ 3) := by
  obtain ⟨ha, ha', hb, hb'⟩ := rectangle_length_bounds hT
  have hT₀ : (0 : ℝ) ≤ T := by exact_mod_cast (show 0 ≤ T by omega)
  exact cramerBoxBudget_le hQ θ
    (by exact_mod_cast (div_nonneg hT₀ (by norm_num)).trans ha)
    (by exact_mod_cast (div_nonneg hT₀ (by norm_num)).trans hb)
    (by exact_mod_cast ha') (by exact_mod_cast hb')

/-- When the explicitly bounded truncation error is small on the selected
scales, the finite model has the required uniform positive main term. -/
theorem uniformCramerMassLowerBound_of_small_budget
    (cutoff order : ℕ → ℕ)
    (hodd : ∀ᶠ k in atTop, Odd (order k))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
      ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
      cramerTruncationBudget (cutoff k) θ ((2 : ℤ) ^ k) (order k) ≤ ε * (4 : ℝ) ^ k) :
    UniformCramerMassLowerBound cutoff := by
  obtain ⟨d, hd, hmain⟩ := cramerMass_ge_area_sub_budget
  let c : ℝ := d / (15240 * 3149600000)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hodd, hsmall (c / 2) (by positivity), eventually_ge_atTop (34 : ℕ)] with k hodd hk hlarge
  intro θ hθ hlocal
  have hT : (10000000000 : ℤ) ≤ (2 : ℤ) ^ k :=
    (by norm_num : (10000000000 : ℤ) ≤ (2 : ℤ) ^ 34).trans
      (pow_right_mono₀ (by norm_num) hlarge)
  obtain ⟨ha, _, hb, _⟩ := rectangle_length_bounds hT
  have hT₀ : (0 : ℝ) ≤ ↑((2 : ℤ) ^ k) := by exact_mod_cast (show (0 : ℤ) ≤ 2 ^ k by positivity)
  have ha₀ := (div_nonneg hT₀ (by norm_num : (0 : ℝ) ≤ 15240)).trans ha
  have hprod := mul_le_mul ha hb (div_nonneg hT₀ (by norm_num : (0 : ℝ) ≤ 3149600000)) ha₀
  have harea : c * (4 : ℝ) ^ k ≤ d * (rectangleFirstLength ((2 : ℤ) ^ k) : ℝ) *
      (rectangleSecondLength ((2 : ℤ) ^ k) : ℝ) := by
    have hpow : ((↑((2 : ℤ) ^ k) : ℝ)) ^ 2 = (4 : ℝ) ^ k := by
      push_cast
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc
      _ = d * ((↑((2 : ℤ) ^ k) : ℝ) / 15240 * ((↑((2 : ℤ) ^ k) : ℝ) / 3149600000)) := by
        rw [← hpow]
        dsimp [c]
        ring
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hd.le
  linarith only [harea, hmain (cutoff k) θ ((2 : ℤ) ^ k) (order k) hodd hT hlocal, hk θ hθ hlocal]

end Jsp000881
