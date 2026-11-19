module

public import Jsp000881.RectangleMask
import all Jsp000881.RectangleMask
public import Jsp000881.RectangleRadius
import all Jsp000881.RectangleRadius
public import Jsp000881.LatticeArea
import all Jsp000881.LatticeArea

public section

namespace Jsp000881

open scoped BigOperators

def castRectanglePoint (p : ℕ) (nm : ℤ × ℤ) : ZMod p × ZMod p :=
  (nm.1, nm.2)

noncomputable def fieldRectangleMask (p : ℕ) (T : ℤ) (x : ZMod p × ZMod p) : ℂ :=
  sideMask p (rectangleFirstStart T) (rectangleFirstLength T) x.1 *
    sideMask p rectangleSecondStart (rectangleSecondLength T) x.2

noncomputable def rectangleMask (p : ℕ) (T : ℤ) (nm : ℤ × ℤ) : ℝ :=
  (sideMask p (rectangleFirstStart T) (rectangleFirstLength T) (nm.1 : ZMod p)).re *
    (sideMask p rectangleSecondStart (rectangleSecondLength T) (nm.2 : ZMod p)).re

theorem fieldRectangleMask_cast (p : ℕ) (T : ℤ) (nm : ℤ × ℤ) :
    fieldRectangleMask p T (castRectanglePoint p nm) = (rectangleMask p T nm : ℂ) := by
  unfold fieldRectangleMask rectangleMask castRectanglePoint
  rw [Complex.ofReal_mul, ← sideMask_eq_ofReal_re, ← sideMask_eq_ofReal_re]

theorem rectangleMask_bounds (p : ℕ) (T : ℤ) (nm : ℤ × ℤ) :
    0 ≤ rectangleMask p T nm ∧ rectangleMask p T nm ≤ 1 := by
  obtain ⟨ha, ha'⟩ := sideMask_re_bounds p (rectangleFirstStart T) (rectangleFirstLength T) ↑nm.1
  obtain ⟨hb, hb'⟩ := sideMask_re_bounds p rectangleSecondStart (rectangleSecondLength T) ↑nm.2
  exact ⟨mul_nonneg ha hb, mul_le_one₀ ha' hb hb'⟩

theorem rectangleMask_ge_quarter {p : ℕ} {T : ℤ} {nm : ℤ × ℤ}
    (hp₁ : sideMaskRadius (rectangleFirstLength T) < p)
    (hp₂ : sideMaskRadius (rectangleSecondLength T) < p)
    (ha : nm.1 ∈ interval (sideMaskCoreStart (rectangleFirstStart T) (rectangleFirstLength T))
      (sideMaskCoreLength (rectangleFirstLength T)))
    (hb : nm.2 ∈ interval (sideMaskCoreStart rectangleSecondStart (rectangleSecondLength T))
      (sideMaskCoreLength (rectangleSecondLength T))) :
    (1 : ℝ) / 4 ≤ rectangleMask p T nm := by
  have h₁ := sideMask_re_ge_half_of_mem_core hp₁ ha
  have h₂ := sideMask_re_ge_half_of_mem_core hp₂ hb
  have h := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans h₁)
  simpa only [rectangleMask, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] using h

theorem fieldRectangleMask_support {p : ℕ} {T : ℤ} (hT : 0 ≤ T)
    (ha : 1 ≤ rectangleFirstLength T) (hb : 1 ≤ rectangleSecondLength T)
    {x : ZMod p × ZMod p} (hx : fieldRectangleMask p T x ≠ 0) :
    ∃ nm ∈ latticeRectangle T, castRectanglePoint p nm = x := by
  have h₁ : sideMask p (rectangleFirstStart T) (rectangleFirstLength T) x.1 ≠ 0 := by
    intro h
    apply hx
    simp only [fieldRectangleMask, h, zero_mul]
  have h₂ : sideMask p rectangleSecondStart (rectangleSecondLength T) x.2 ≠ 0 := by
    intro h
    apply hx
    simp only [fieldRectangleMask, h, mul_zero]
  obtain ⟨a, ha', he₁⟩ := sideMask_support (s := rectangleFirstStart T) ha h₁
  obtain ⟨b, hb', he₂⟩ := sideMask_support (s := rectangleSecondStart) hb h₂
  refine ⟨(a, b), ?_, Prod.ext he₁.symm he₂.symm⟩
  rw [latticeRectangle_eq_intervals hT, Finset.product_eq_sprod]
  exact Finset.mem_product.mpr ⟨ha', hb'⟩

private theorem intCast_inj_of_abs_le {p : ℕ} {R a b : ℤ} (hp : 2 * R < (p : ℤ))
    (ha : |a| ≤ R) (hb : |b| ≤ R) (he : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hd : (p : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
    rw [Int.cast_sub, he, sub_self])
  by_contra hab
  have hlarge := Int.le_abs_of_dvd (sub_ne_zero.mpr hab) hd
  have hsmall := (abs_sub a b).trans (add_le_add ha hb)
  omega

theorem castRectanglePoint_injOn {p : ℕ} {T R : ℤ} (hp : 2 * R < (p : ℤ))
    (hR : ∀ nm ∈ latticeRectangle T, |nm.1| ≤ R ∧ |nm.2| ≤ R) :
    Set.InjOn (castRectanglePoint p) (latticeRectangle T : Set (ℤ × ℤ)) := by
  intro a ha b hb he
  obtain ⟨ha₁, ha₂⟩ := hR a ha
  obtain ⟨hb₁, hb₂⟩ := hR b hb
  exact Prod.ext (intCast_inj_of_abs_le hp ha₁ hb₁ (congrArg Prod.fst he))
    (intCast_inj_of_abs_le hp ha₂ hb₂ (congrArg Prod.snd he))

/-- The masked lattice sum is exactly the full finite-field sum. -/
theorem fieldRectangle_sum {p : ℕ} [NeZero p] {T R : ℤ}
    (hT : 0 ≤ T) (ha : 1 ≤ rectangleFirstLength T) (hb : 1 ≤ rectangleSecondLength T)
    (hp : 2 * R < (p : ℤ)) (hR : ∀ nm ∈ latticeRectangle T, |nm.1| ≤ R ∧ |nm.2| ≤ R)
    (F : ZMod p × ZMod p → ℂ) :
    (∑ x, fieldRectangleMask p T x * F x) =
      ∑ nm ∈ latticeRectangle T, (rectangleMask p T nm : ℂ) * F (castRectanglePoint p nm) := by
  classical
  let U := (latticeRectangle T).image (castRectanglePoint p)
  symm
  calc
    _ = ∑ nm ∈ latticeRectangle T, fieldRectangleMask p T (castRectanglePoint p nm) *
        F (castRectanglePoint p nm) := by
      apply Finset.sum_congr rfl
      intro nm _
      rw [fieldRectangleMask_cast]
    _ = ∑ x ∈ U, fieldRectangleMask p T x * F x :=
      (Finset.sum_image (f := fun x => fieldRectangleMask p T x * F x)
        (castRectanglePoint_injOn hp hR)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hx'
      have hz : fieldRectangleMask p T x = 0 := by
        by_contra he
        obtain ⟨nm, hnm, he'⟩ := fieldRectangleMask_support hT ha hb he
        exact hx' (Finset.mem_image.mpr ⟨nm, hnm, he'⟩)
      rw [hz, zero_mul]

end Jsp000881
