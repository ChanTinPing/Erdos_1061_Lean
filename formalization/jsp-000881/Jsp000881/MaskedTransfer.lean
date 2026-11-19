module

public import Jsp000881.CramerMass
import all Jsp000881.CramerMass

public section

namespace Jsp000881

open Filter
open scoped BigOperators

noncomputable def maskedRectangleMass (mask : ℤ × ℤ → ℝ) (Q : ℕ) (θ : PlaneIndex) (T : ℤ)
    (j : ℕ) : ℝ :=
  ∑ nm ∈ latticeRectangle T, mask nm * ∏ i : Fin 6,
    if i.val < j then primeWeight ((sextupleOn θ nm).coord i)
    else cramerWeight Q ((sextupleOn θ nm).coord i)

theorem maskedRectangleMass_step (mask : ℤ × ℤ → ℝ) (Q : ℕ) (θ : PlaneIndex) (T : ℤ) (j : Fin 6) :
    maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val =
      ∑ nm ∈ latticeRectangle T, mask nm *
        ((primeWeight ((sextupleOn θ nm).coord j) - cramerWeight Q ((sextupleOn θ nm).coord j)) *
          ∏ i ∈ Finset.univ.erase j,
            if i.val < j.val then primeWeight ((sextupleOn θ nm).coord i)
            else cramerWeight Q ((sextupleOn θ nm).coord i)) := by
  unfold maskedRectangleMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro nm _
  rw [← mul_sub, mixedProduct_step]

private theorem primeWeight_nonneg (n : ℤ) : 0 ≤ primeWeight n := by
  unfold primeWeight
  split
  · rename_i hp
    have hp₂ := Nat.Prime.two_le hp
    exact Real.log_nonneg (by exact_mod_cast (show (1 : ℤ) ≤ n by omega))
  · exact le_rfl

private theorem cramerWeight_nonneg (Q : ℕ) (n : ℤ) : 0 ≤ cramerWeight Q n := by
  unfold cramerWeight
  split
  · exact (cramerNormalization_pos Q).le
  · exact le_rfl

theorem maskedRectangleMass_six_le {mask : ℤ × ℤ → ℝ} {Q : ℕ} {θ : PlaneIndex} {T : ℤ}
    (hmask : ∀ nm ∈ latticeRectangle T, mask nm ≤ 1) :
    maskedRectangleMass mask Q θ T 6 ≤ rectanglePrimeMass θ T := by
  simp only [maskedRectangleMass, rectanglePrimeMass, Fin.isLt, if_true]
  apply Finset.sum_le_sum
  intro nm hnm
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmask nm hnm)
    (Finset.prod_nonneg fun _ _ => primeWeight_nonneg _)

/-- A mask bounded below on an inner box gives the same positive Cramér
area coefficient, multiplied by the lower bound for the mask. -/
theorem maskedCramerMass_ge_box_area_sub_budget :
    ∃ d : ℝ, 0 < d ∧ ∀ (Q : ℕ) (θ : PlaneIndex) (T s a t b : ℤ) (L : ℕ)
      (mask : ℤ × ℤ → ℝ) (ρ : ℝ),
      Odd L → 0 ≤ a → 0 ≤ b → LocallyAdmissible θ → 0 ≤ ρ →
      (interval s a).product (interval t b) ⊆ latticeRectangle T →
      (∀ nm ∈ latticeRectangle T, 0 ≤ mask nm) →
      (∀ nm ∈ (interval s a).product (interval t b), ρ ≤ mask nm) →
      ρ * (d * (a : ℝ) * (b : ℝ) - cramerBoxBudget Q θ a b L) ≤
        maskedRectangleMass mask Q θ T 0 := by
  obtain ⟨d, hd, hmain⟩ := cramerMass_ge_box_area_sub_budget
  refine ⟨d, hd, ?_⟩
  intro Q θ T s a t b L mask ρ hL ha hb hθ hρ hsub hpos hcentral
  let Y := (interval s a).product (interval t b)
  let w := fun nm : ℤ × ℤ => ∏ i : Fin 6, cramerWeight Q ((sextupleOn θ nm).coord i)
  have hw (nm) : 0 ≤ w nm := Finset.prod_nonneg fun _ _ => cramerWeight_nonneg _ _
  calc
    _ ≤ ρ * ∑ nm ∈ Y, w nm := mul_le_mul_of_nonneg_left (hmain Q θ s a t b L hL ha hb hθ) hρ
    _ = ∑ nm ∈ Y, ρ * w nm := by rw [Finset.mul_sum]
    _ ≤ ∑ nm ∈ Y, mask nm * w nm :=
      Finset.sum_le_sum fun nm hn => mul_le_mul_of_nonneg_right (hcentral nm hn) (hw nm)
    _ ≤ ∑ nm ∈ latticeRectangle T, mask nm * w nm :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun nm hn _ => mul_nonneg (hpos nm hn) (hw nm)
    _ = _ := by simp only [maskedRectangleMass, Nat.not_lt_zero, if_false, w]

/-- Transferring a positive masked model main term yields the unmasked
prime lower bound needed by the original problem. -/
theorem weightedPrimeRectangleLowerBound_of_mask {cutoff : ℕ → ℕ} {mask : ℕ → ℤ × ℤ → ℝ}
    (hmask : ∀ k nm, mask k nm ≤ 1)
    (hmain : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
      ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
      c * (4 : ℝ) ^ k ≤ maskedRectangleMass (mask k) (cutoff k) θ ((2 : ℤ) ^ k) 0)
    (herror : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
      ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ → ∀ j < 6,
      |maskedRectangleMass (mask k) (cutoff k) θ ((2 : ℤ) ^ k) (j + 1) -
        maskedRectangleMass (mask k) (cutoff k) θ ((2 : ℤ) ^ k) j| ≤ ε * (4 : ℝ) ^ k) :
    WeightedPrimeRectangleLowerBound := by
  obtain ⟨c, hc, hmain⟩ := hmain
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmain, herror (c / 12) (by positivity)] with k hk he
  intro θ hθ hlocal
  let f := maskedRectangleMass (mask k) (cutoff k) θ ((2 : ℤ) ^ k)
  have hlow : c * (4 : ℝ) ^ k ≤ f 0 := hk θ hθ hlocal
  have h₁ := (abs_le.mp (abs_six_step_sub_le f (he θ hθ hlocal))).1
  have h₂ : f 6 ≤ rectanglePrimeMass θ ((2 : ℤ) ^ k) := maskedRectangleMass_six_le fun nm _ => hmask k nm
  linarith only [hlow, h₁, h₂]

end Jsp000881
