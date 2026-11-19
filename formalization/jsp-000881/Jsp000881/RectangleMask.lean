module

public import Jsp000881.SieveBounds
import all Jsp000881.SieveBounds
public import Jsp000881.TriangleInterval
import all Jsp000881.TriangleInterval

public section

namespace Jsp000881

/-- The largest integer radius whose centered support fits in a side. -/
def sideMaskRadius (l : ℤ) : ℕ := ((l - 1) / 2).toNat

def sideMaskCenter (s l : ℤ) : ℤ := s + (sideMaskRadius l : ℤ)

def sideMaskCoreStart (s l : ℤ) : ℤ := sideMaskCenter s l - (sideMaskRadius l : ℤ) / 2

def sideMaskCoreLength (l : ℤ) : ℤ := 2 * ((sideMaskRadius l : ℤ) / 2) + 1

noncomputable def sideMask (p : ℕ) (s l : ℤ) (z : ZMod p) : ℂ :=
  triangleCutoff (triangleInterval p (sideMaskRadius l)) (z - (sideMaskCenter s l : ZMod p))

theorem sideMaskRadius_cast {l : ℤ} (hl : 1 ≤ l) :
    (sideMaskRadius l : ℤ) = (l - 1) / 2 := by
  unfold sideMaskRadius
  exact Int.toNat_of_nonneg (by omega)

theorem sideMaskRadius_lt_length {l : ℤ} (hl : 1 ≤ l) : (sideMaskRadius l : ℤ) < l := by
  rw [sideMaskRadius_cast hl]
  omega

theorem sideMaskCore_Ico (s l : ℤ) :
    interval (sideMaskCoreStart s l) (sideMaskCoreLength l) =
      Finset.Ico (sideMaskCenter s l - (sideMaskRadius l : ℤ) / 2)
        (sideMaskCenter s l + (sideMaskRadius l : ℤ) / 2 + 1) := by
  unfold interval sideMaskCoreStart sideMaskCoreLength
  congr 1
  ring

theorem sideMaskCoreLength_nonneg (l : ℤ) : 0 ≤ sideMaskCoreLength l := by
  unfold sideMaskCoreLength
  have hM : (0 : ℤ) ≤ (sideMaskRadius l : ℤ) := Nat.cast_nonneg _
  omega

theorem sideMaskCore_card (s l : ℤ) :
    ((interval (sideMaskCoreStart s l) (sideMaskCoreLength l)).card : ℝ) =
      (sideMaskCoreLength l : ℝ) :=
  card_interval _ _ (sideMaskCoreLength_nonneg l)

theorem sideMaskCoreLength_ge_quarter {l : ℤ} (hl : 8 ≤ l) : l ≤ 4 * sideMaskCoreLength l := by
  unfold sideMaskCoreLength
  rw [sideMaskRadius_cast (by omega : 1 ≤ l)]
  omega

theorem sideMaskCoreLength_le_length {l : ℤ} (hl : 1 ≤ l) : sideMaskCoreLength l ≤ l := by
  unfold sideMaskCoreLength
  rw [sideMaskRadius_cast hl]
  omega

theorem sideMaskCoreLength_real_ge_quarter {l : ℤ} (hl : 8 ≤ l) :
    (l : ℝ) / 4 ≤ (sideMaskCoreLength l : ℝ) := by
  have h : (l : ℝ) ≤ 4 * (sideMaskCoreLength l : ℝ) := by
    exact_mod_cast sideMaskCoreLength_ge_quarter hl
  linarith only [h]

private theorem center_add_mem_side {s l t : ℤ} (hl : 1 ≤ l)
    (ht : |t| ≤ (sideMaskRadius l : ℤ)) : sideMaskCenter s l + t ∈ interval s l := by
  have hr := sideMaskRadius_cast hl
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  unfold interval sideMaskCenter
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

private theorem mem_sideMaskCore_abs {s l x : ℤ}
    (hx : x ∈ interval (sideMaskCoreStart s l) (sideMaskCoreLength l)) :
    2 * |x - sideMaskCenter s l| ≤ (sideMaskRadius l : ℤ) := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hx
  unfold sideMaskCoreStart at hlo hhi
  unfold sideMaskCoreLength at hhi
  have h : |x - sideMaskCenter s l| ≤ (sideMaskRadius l : ℤ) / 2 :=
    abs_le.mpr ⟨by omega, by omega⟩
  have h₂ := mul_le_mul_of_nonneg_left h (by decide : (0 : ℤ) ≤ 2)
  omega

theorem sideMaskCore_subset_side {s l : ℤ} (hl : 1 ≤ l) :
    interval (sideMaskCoreStart s l) (sideMaskCoreLength l) ⊆ interval s l := by
  intro x hx
  have hbound := mem_sideMaskCore_abs hx
  have hm : (0 : ℤ) ≤ (sideMaskRadius l : ℤ) := Nat.cast_nonneg _
  have hy := center_add_mem_side (s := s) hl (show |x - sideMaskCenter s l| ≤ (sideMaskRadius l : ℤ) by omega)
  rw [show sideMaskCenter s l + (x - sideMaskCenter s l) = x by ring] at hy
  exact hy

theorem sideMask_re_bounds (p : ℕ) (s l : ℤ) (z : ZMod p) :
    0 ≤ (sideMask p s l z).re ∧ (sideMask p s l z).re ≤ 1 :=
  triangleCutoff_re_bounds _ _

private theorem cutoff_eq_ofReal_re {K : Type*} [Add K] (E : Finset K) (t : K) :
    triangleCutoff E t = ((triangleCutoff E t).re : ℂ) := by
  rw [triangleCutoff_re_eq]
  unfold triangleCutoff
  push_cast <;> rfl

theorem sideMask_eq_ofReal_re (p : ℕ) (s l : ℤ) (z : ZMod p) :
    sideMask p s l z = ((sideMask p s l z).re : ℂ) :=
  cutoff_eq_ofReal_re _ _

/-- At each point of the central side interval, the real cutoff is at least one half. -/
theorem sideMask_re_ge_half_of_mem_core {p : ℕ} {s l x : ℤ} (hp : sideMaskRadius l < p)
    (hx : x ∈ interval (sideMaskCoreStart s l) (sideMaskCoreLength l)) :
    (1 : ℝ) / 2 ≤ (sideMask p s l (x : ZMod p)).re := by
  simpa only [sideMask, Int.cast_sub] using
    triangleInterval_re_ge_half hp (x - sideMaskCenter s l) (mem_sideMaskCore_abs hx)

/-- Any modular point with nonzero mask is the image of an integer on the original side. -/
theorem sideMask_support {p : ℕ} {s l : ℤ} (hl : 1 ≤ l) {z : ZMod p}
    (h : sideMask p s l z ≠ 0) : ∃ x ∈ interval s l, z = (x : ZMod p) := by
  obtain ⟨t, ht, he⟩ := triangleInterval_translate_support
    (p := p) (M := sideMaskRadius l) (c := (sideMaskCenter s l : ZMod p)) h
  exact ⟨sideMaskCenter s l + t, center_add_mem_side hl ht, by simpa only [Int.cast_add] using he⟩

end Jsp000881
