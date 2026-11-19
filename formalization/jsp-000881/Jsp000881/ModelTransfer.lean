module

public import Jsp000881.PrimeWeights
import all Jsp000881.PrimeWeights
public import PrimeUniformity.Weights

public section

namespace Jsp000881

export PrimeUniformity (cramerPrimeSet cramerNormalization cramerWeight)

open Filter
open scoped BigOperators

/-- Replace the first `j` Cramér factors by the prime-supported weight. -/
noncomputable def mixedRectangleMass (Q : ℕ) (θ : PlaneIndex) (T : ℤ) (j : ℕ) : ℝ :=
  ∑ nm ∈ latticeRectangle T, ∏ i : Fin 6,
    if i.val < j then primeWeight ((sextupleOn θ nm).coord i)
    else cramerWeight Q ((sextupleOn θ nm).coord i)

theorem mixedRectangleMass_six (Q : ℕ) (θ : PlaneIndex) (T : ℤ) :
    mixedRectangleMass Q θ T 6 = rectanglePrimeMass θ T := by
  simp [mixedRectangleMass, rectanglePrimeMass, Fin.isLt]

/-- One replacement extracts precisely one real-prime minus Cramér factor
from the product over the six affine forms. -/
theorem mixedProduct_step (a b : Fin 6 → ℝ) (j : Fin 6) :
    (∏ i : Fin 6, if i.val < j.val + 1 then a i else b i) -
      (∏ i : Fin 6, if i.val < j.val then a i else b i) =
        (a j - b j) * ∏ i ∈ Finset.univ.erase j, if i.val < j.val then a i else b i := by
  let w := fun (m : ℕ) (i : Fin 6) => if i.val < m then a i else b i
  change (∏ i, w (j.val + 1) i) - (∏ i, w j.val i) =
    (a j - b j) * ∏ i ∈ Finset.univ.erase j, w j.val i
  have huv : j ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ j
  have hrest : (∏ i ∈ Finset.univ.erase j, w (j.val + 1) i) =
      ∏ i ∈ Finset.univ.erase j, w j.val i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i.val ≠ j.val := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    by_cases hbefore : i.val < j.val
    · simp only [w, if_pos hbefore, if_pos (hbefore.trans (Nat.lt_succ_self _))]
    · have hnot : ¬ i.val < j.val + 1 := by omega
      simp only [w, if_neg hbefore, if_neg hnot]
  rw [← Finset.mul_prod_erase _ (w (j.val + 1)) huv, ← Finset.mul_prod_erase _ (w j.val) huv, hrest]
  simp only [w, Nat.lt_succ_self, if_true, lt_irrefl, if_false, sub_mul]

theorem mixedRectangleMass_step (Q : ℕ) (θ : PlaneIndex) (T : ℤ) (j : Fin 6) :
    mixedRectangleMass Q θ T (j.val + 1) - mixedRectangleMass Q θ T j.val =
      ∑ nm ∈ latticeRectangle T,
        (primeWeight ((sextupleOn θ nm).coord j) - cramerWeight Q ((sextupleOn θ nm).coord j)) *
          ∏ i ∈ Finset.univ.erase j,
            if i.val < j.val then primeWeight ((sextupleOn θ nm).coord i)
            else cramerWeight Q ((sextupleOn θ nm).coord i) := by
  unfold mixedRectangleMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro nm _
  exact mixedProduct_step (fun i => primeWeight ((sextupleOn θ nm).coord i))
    (fun i => cramerWeight Q ((sextupleOn θ nm).coord i)) j

theorem abs_six_step_sub_le (f : ℕ → ℝ) {e : ℝ} (h : ∀ j < 6, |f (j + 1) - f j| ≤ e) :
    |f 6 - f 0| ≤ 6 * e := by
  rw [← Finset.sum_range_sub f 6]
  calc
    _ ≤ ∑ j ∈ Finset.range 6, |f (j + 1) - f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range 6, e := Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
    _ = _ := by simp

theorem abs_mass_sub_cramer_le {Q : ℕ} {θ : PlaneIndex} {T : ℤ} {e : ℝ}
    (h : ∀ j < 6, |mixedRectangleMass Q θ T (j + 1) - mixedRectangleMass Q θ T j| ≤ e) :
    |rectanglePrimeMass θ T - mixedRectangleMass Q θ T 0| ≤ 6 * e := by
  rw [← mixedRectangleMass_six (Q := Q)]
  exact abs_six_step_sub_le _ h

def UniformCramerMassLowerBound (cutoff : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
    ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
    c * (4 : ℝ) ^ k ≤ mixedRectangleMass (cutoff k) θ ((2 : ℤ) ^ k) 0

def UniformRectangleReplacementError (cutoff : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
    ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ → ∀ j < 6,
    |mixedRectangleMass (cutoff k) θ ((2 : ℤ) ^ k) (j + 1) -
      mixedRectangleMass (cutoff k) θ ((2 : ℤ) ^ k) j| ≤ ε * (4 : ℝ) ^ k

/-- Six single-factor replacement estimates suffice to transfer any strictly
positive Cramér main term to the weighted prime-count statement. -/
theorem weightedPrimeRectangleLowerBound_of_model {cutoff : ℕ → ℕ}
    (hmain : UniformCramerMassLowerBound cutoff)
    (herror : UniformRectangleReplacementError cutoff) :
    WeightedPrimeRectangleLowerBound := by
  obtain ⟨c, hc, hmain⟩ := hmain
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmain, herror (c / 12) (by positivity)] with k hmain herror
  intro θ hbox hlocal
  have h₁ := hmain θ hbox hlocal
  have h₂ := abs_mass_sub_cramer_le (herror θ hbox hlocal)
  have h₃ := (abs_le.mp h₂).1
  linarith only [h₁, h₃]

end Jsp000881
