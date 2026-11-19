module

public import Jsp000881.RectangleField
import all Jsp000881.RectangleField
public import Jsp000881.MaskedTransfer
import all Jsp000881.MaskedTransfer
public import Jsp000881.PrimeCutoffGrowth
import all Jsp000881.PrimeCutoffGrowth

public section

namespace Jsp000881

open Filter
open scoped Topology

theorem large_dyadic_rectangle {k : ℕ} (hk : 40 ≤ k) :
    (10000000000 : ℤ) ≤ (2 : ℤ) ^ k ∧
      8 ≤ rectangleFirstLength ((2 : ℤ) ^ k) ∧ 8 ≤ rectangleSecondLength ((2 : ℤ) ^ k) := by
  have hT : (100000000000 : ℤ) ≤ (2 : ℤ) ^ k :=
    (by norm_num : (100000000000 : ℤ) ≤ (2 : ℤ) ^ 40).trans
      (pow_right_mono₀ (by norm_num) hk)
  have hT' : (10000000000 : ℤ) ≤ (2 : ℤ) ^ k := le_trans (by decide) hT
  obtain ⟨h₁, _, h₂, _⟩ := rectangle_length_bounds hT'
  have hTr : (100000000000 : ℝ) ≤ ↑((2 : ℤ) ^ k) := by exact_mod_cast hT
  refine ⟨hT', ?_, ?_⟩
  · exact_mod_cast (show (8 : ℝ) ≤ (rectangleFirstLength ((2 : ℤ) ^ k) : ℝ) from by linarith only [hTr, h₁])
  · exact_mod_cast (show (8 : ℝ) ≤ (rectangleSecondLength ((2 : ℤ) ^ k) : ℝ) from by linarith only [hTr, h₂])

theorem eventually_radius_cutoff :
    ∀ᶠ k : ℕ in atTop, 1 ≤ primeUniformityCutoff (primeRectangleRadius k) ∧
      primeUniformityCutoff (primeRectangleRadius k) ≤ 2 ^ primeCutoffDyadicIndex k ∧
      primeCutoffDyadicIndex k ^ 4 ≤ k := by
  apply eventually_primeUniformityCutoff_dyadic_growth (show (0 : ℝ) < 5000 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact ⟨primeRectangleRadius_pos hk, log_primeRectangleRadius_le hk⟩

private theorem core_area_lower {k : ℕ} {d : ℝ} (hk : 40 ≤ k) (hd : 0 ≤ d) :
    (d / (16 * 15240 * 3149600000)) * (4 : ℝ) ^ k ≤
      d * (sideMaskCoreLength (rectangleFirstLength ((2 : ℤ) ^ k)) : ℝ) *
        (sideMaskCoreLength (rectangleSecondLength ((2 : ℤ) ^ k)) : ℝ) := by
  let T := (2 : ℤ) ^ k
  obtain ⟨hT, ha, hb⟩ := large_dyadic_rectangle hk
  obtain ⟨ha₁, _, hb₁, _⟩ := rectangle_length_bounds hT
  have hAr : (T : ℝ) / (4 * 15240) ≤ (sideMaskCoreLength (rectangleFirstLength T) : ℝ) :=
    (by linarith only [ha₁, sideMaskCoreLength_real_ge_quarter ha])
  have hBr : (T : ℝ) / (4 * 3149600000) ≤ (sideMaskCoreLength (rectangleSecondLength T) : ℝ) :=
    (by linarith only [hb₁, sideMaskCoreLength_real_ge_quarter hb])
  have hTr : (0 : ℝ) ≤ T := by exact_mod_cast (show 0 ≤ T by positivity)
  have hA₀ : (0 : ℝ) ≤ sideMaskCoreLength (rectangleFirstLength T) :=
    by exact_mod_cast sideMaskCoreLength_nonneg (rectangleFirstLength T)
  have h₂ : ((T : ℝ)) ^ 2 = (4 : ℝ) ^ k := by
    dsimp [T]
    push_cast
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  calc
    _ = d * ((T : ℝ) / (4 * 15240) * ((T : ℝ) / (4 * 3149600000))) := by
      rw [← h₂]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul hAr hBr (div_nonneg hTr (by norm_num)) hA₀) hd

theorem maskedCramerMass_at_rectangleRadius (p : ℕ → ℕ)
    (hp : ∀ᶠ k : ℕ in atTop, 32 * primeRectangleRadius k < p k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
      ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
      c * (4 : ℝ) ^ k ≤
        maskedRectangleMass (rectangleMask (p k) ((2 : ℤ) ^ k))
          (primeUniformityCutoff (primeRectangleRadius k)) θ ((2 : ℤ) ^ k) 0 := by
  obtain ⟨d, hd, hmain⟩ := maskedCramerMass_ge_box_area_sub_budget
  let c₀ := d / (16 * 15240 * 3149600000)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀ / 8, by positivity, ?_⟩
  have ht : Tendsto (fun k => 4 * (1 / 2 : ℝ) ^ primeCutoffDyadicIndex k) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    simpa only [mul_zero, Function.comp_apply] using (h.comp tendsto_primeCutoffDyadicIndex).const_mul 4
  filter_upwards [hp, eventually_ge_atTop (40 : ℕ), eventually_radius_cutoff,
    tendsto_primeCutoffDyadicIndex.eventually (eventually_ge_atTop (4000 : ℕ)),
    (tendsto_order.1 ht).2 (c₀ / 2) (by positivity)] with k hpk hk hcut hNk herr
  intro θ _ hθ
  let T := (2 : ℤ) ^ k
  let Q := primeUniformityCutoff (primeRectangleRadius k)
  let N := primeCutoffDyadicIndex k
  let a := rectangleFirstLength T
  let b := rectangleSecondLength T
  let s := rectangleFirstStart T
  let t := rectangleSecondStart
  let A := sideMaskCoreLength a
  let B := sideMaskCoreLength b
  let u := sideMaskCoreStart s a
  let v := sideMaskCoreStart t b
  obtain ⟨hT, ha, hb⟩ := large_dyadic_rectangle hk
  obtain ⟨_, ha₂, _, hb₂⟩ := rectangle_length_bounds hT
  have ha₃ : a ≤ T := by exact_mod_cast ha₂
  have hb₃ : b ≤ T := by exact_mod_cast hb₂
  have ha' : 1 ≤ a := le_trans (by decide : (1 : ℤ) ≤ 8) ha
  have hb' : 1 ≤ b := le_trans (by decide : (1 : ℤ) ≤ 8) hb
  have hT₀ : 0 ≤ T := by positivity
  have hk₁ : 1 ≤ k := le_trans (by decide : (1 : ℕ) ≤ 40) hk
  have hbound : T < (p k : ℤ) := by
    have hR := dyadicHeight_le_primeRectangleRadius hk₁
    have hpk' : 32 * (primeRectangleRadius k : ℤ) < (p k : ℤ) := by exact_mod_cast hpk
    have hR₀ : 0 ≤ (primeRectangleRadius k : ℤ) := Nat.cast_nonneg _
    omega
  have hpa : sideMaskRadius a < p k := by
    have hh := (sideMaskRadius_lt_length ha').trans_le ha₃
    exact_mod_cast hh.trans hbound
  have hpb : sideMaskRadius b < p k := by
    have hh := (sideMaskRadius_lt_length hb').trans_le hb₃
    exact_mod_cast hh.trans hbound
  have hsub : (interval u A).product (interval v B) ⊆ latticeRectangle T := by
    rw [latticeRectangle_eq_intervals hT₀, Finset.product_eq_sprod, Finset.product_eq_sprod]
    exact Finset.product_subset_product (sideMaskCore_subset_side ha') (sideMaskCore_subset_side hb')
  have hM := hmain Q θ T u A v B (cramerDyadicOrder N) (rectangleMask (p k) T) (1 / 4)
    (cramerDyadicOrder_odd N) (sideMaskCoreLength_nonneg a) (sideMaskCoreLength_nonneg b)
    hθ (by norm_num) hsub (fun nm _ => (rectangleMask_bounds _ _ _).1) (by
      intro nm hn
      rw [Finset.product_eq_sprod, Finset.mem_product] at hn
      exact rectangleMask_ge_quarter hpa hpb hn.1 hn.2)
  have hB := cramerBoxBudget_le_dyadic hcut.1 hcut.2.1 hNk hcut.2.2 θ hθ
    (sideMaskCoreLength_nonneg a) (sideMaskCoreLength_nonneg b)
    ((sideMaskCoreLength_le_length ha').trans ha₃) ((sideMaskCoreLength_le_length hb').trans hb₃)
  have herr' : cramerBoxBudget Q θ A B (cramerDyadicOrder N) ≤ (c₀ / 2) * (4 : ℝ) ^ k :=
    hB.trans (mul_le_mul_of_nonneg_right herr.le (by positivity))
  have harea : c₀ * (4 : ℝ) ^ k ≤ d * (A : ℝ) * (B : ℝ) := core_area_lower hk hd.le
  linarith only [hM, harea, herr']

end Jsp000881
