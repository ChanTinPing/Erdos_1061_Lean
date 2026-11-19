module

public import Jsp000881.Rectangles
import all Jsp000881.Rectangles
public import Jsp000881.SieveBounds
import all Jsp000881.SieveBounds

public section

namespace Jsp000881

def rectangleFirstStart (T : ℤ) : ℤ := -(2 * T / 7620)

private def firstStop (T : ℤ) : ℤ := (-T) / 7620 + 1

def rectangleSecondStart : ℤ := -7

private def secondStop (T : ℤ) : ℤ := (T - 12145800000) / 1574800000 + 1

def rectangleFirstLength (T : ℤ) : ℤ := firstStop T - rectangleFirstStart T

def rectangleSecondLength (T : ℤ) : ℤ := secondStop T - rectangleSecondStart

theorem latticeRectangle_eq_intervals {T : ℤ} (hT : 0 ≤ T) :
    latticeRectangle T =
      (interval (rectangleFirstStart T) (rectangleFirstLength T)).product
      (interval rectangleSecondStart (rectangleSecondLength T)) := by
  ext nm
  rw [mem_latticeRectangle hT, Finset.product_eq_sprod, Finset.mem_product, interval, interval,
    Finset.mem_Ico, Finset.mem_Ico]
  rw [show rectangleFirstStart T + rectangleFirstLength T = firstStop T by
    unfold rectangleFirstLength; ring,
    show rectangleSecondStart + rectangleSecondLength T = secondStop T by
    unfold rectangleSecondLength; ring]
  unfold InRectangle
  have h₁ : rectangleFirstStart T ≤ nm.1 ↔ -(15 * (508 * nm.1)) ≤ 2 * T := by
    unfold rectangleFirstStart
    rw [Int.neg_le_iff]
    exact (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 7620)).trans (by omega)
  have h₂ : nm.1 < firstStop T ↔ T ≤ -(15 * (508 * nm.1)) := by
    unfold firstStop
    rw [← Int.le_iff_lt_add_one, Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 7620)]
    omega
  have h₃ : rectangleSecondStart ≤ nm.2 ↔ 0 ≤ 31 * (3918 + 508 * nm.2) := by unfold rectangleSecondStart; omega
  have h₄ : nm.2 < secondStop T ↔ 100000 * (31 * (3918 + 508 * nm.2)) ≤ T := by
    unfold secondStop
    rw [← Int.le_iff_lt_add_one, Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 1574800000)]
    omega
  rw [h₁, h₂, h₃, h₄]
  tauto

theorem rectangle_length_bounds {T : ℤ} (hT : 10000000000 ≤ T) :
    (T : ℝ) / 15240 ≤ (rectangleFirstLength T : ℝ) ∧
      (rectangleFirstLength T : ℝ) ≤ (T : ℝ) ∧
      (T : ℝ) / 3149600000 ≤ (rectangleSecondLength T : ℝ) ∧
      (rectangleSecondLength T : ℝ) ≤ (T : ℝ) := by
  have hp : (0 : ℤ) < 7620 := by decide
  have hq : (0 : ℤ) < 1574800000 := by decide
  have hlower₁ : -T < firstStop T * 7620 := Int.lt_ediv_add_one_mul_self (-T) hp
  have hupper₁ := Int.ediv_mul_le (-T) hp.ne'
  have hlower₂ := Int.lt_ediv_add_one_mul_self (2 * T) hp
  have hupper₂ := Int.ediv_mul_le (2 * T) hp.ne'
  have hlower₃ : T - 12145800000 < secondStop T * 1574800000 :=
    Int.lt_ediv_add_one_mul_self (T - 12145800000) hq
  have hupper₃ := Int.ediv_mul_le (T - 12145800000) hq.ne'
  have hlo₁ : T ≤ rectangleFirstLength T * 15240 := by
    unfold rectangleFirstLength firstStop rectangleFirstStart at *
    omega
  have hhi₁ : rectangleFirstLength T ≤ T := by
    unfold rectangleFirstLength firstStop rectangleFirstStart at *
    omega
  have hlo₂ : T ≤ rectangleSecondLength T * 3149600000 := by
    unfold rectangleSecondLength rectangleSecondStart secondStop at *
    omega
  have hhi₂ : rectangleSecondLength T ≤ T := by
    unfold rectangleSecondLength rectangleSecondStart secondStop at *
    omega
  exact ⟨(div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast hlo₁), by exact_mod_cast hhi₁,
    (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast hlo₂), by exact_mod_cast hhi₂⟩

/-- Fixed rectangle volume constants in the integer lattice coordinates. -/
theorem card_latticeRectangle_bounds {T : ℤ} (hT : 10000000000 ≤ T) :
    (T : ℝ) ^ 2 / (15240 * 3149600000) ≤ ((latticeRectangle T).card : ℝ) ∧
      ((latticeRectangle T).card : ℝ) ≤ (T : ℝ) ^ 2 := by
  obtain ⟨hl₁, hu₁, hl₂, hu₂⟩ := rectangle_length_bounds hT
  have hT' : (0 : ℝ) ≤ T := by exact_mod_cast (show 0 ≤ T by omega)
  have h₁ : 0 ≤ rectangleFirstLength T := by
    exact_mod_cast ((div_nonneg hT' (by norm_num)).trans hl₁)
  have h₂ : 0 ≤ rectangleSecondLength T := by
    exact_mod_cast ((div_nonneg hT' (by norm_num)).trans hl₂)
  rw [latticeRectangle_eq_intervals (by omega), Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul,
    card_interval _ _ h₁, card_interval _ _ h₂]
  constructor
  · have he : (T : ℝ) ^ 2 / (15240 * 3149600000) = ((T : ℝ) / 15240) * ((T : ℝ) / 3149600000) := by
      ring
    rw [he]
    exact mul_le_mul hl₁ hl₂ (by positivity) (by exact_mod_cast h₁)
  · rw [pow_two]
    exact mul_le_mul hu₁ hu₂ (by exact_mod_cast h₂) hT'

end Jsp000881
