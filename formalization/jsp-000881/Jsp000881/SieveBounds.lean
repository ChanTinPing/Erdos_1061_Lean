module

public import PrimeUniformity.ResidueIntervals
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Jsp000881

open scoped BigOperators

export PrimeUniformity (interval card_interval residueSlice card_residueSlice_le)

/-- A slice for each value of the free coordinate, with one permitted residue
in each of the other two coordinates. -/
noncomputable def twoResidueCover {p : ℕ} (U : Finset ℤ) (start₁ len₁ start₂ len₂ : ℤ)
    (r₁ r₂ : ℤ → ZMod p) : Finset (ℤ × ℤ × ℤ) :=
  U.biUnion fun u =>
    ({u} : Finset ℤ).product
      ((residueSlice start₁ len₁ (r₁ u)).product (residueSlice start₂ len₂ (r₂ u)))

theorem mem_twoResidueCover {p : ℕ} {U : Finset ℤ} {start₁ len₁ start₂ len₂ : ℤ}
    {r₁ r₂ : ℤ → ZMod p} {u v w : ℤ} (hu : u ∈ U)
    (hv : v ∈ interval start₁ len₁) (hw : w ∈ interval start₂ len₂)
    (hv' : (v : ZMod p) = r₁ u) (hw' : (w : ZMod p) = r₂ u) :
    (u, v, w) ∈ twoResidueCover U start₁ len₁ start₂ len₂ r₁ r₂ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_product.mpr ⟨Finset.mem_singleton_self u,
    Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hv, hv'⟩, Finset.mem_filter.mpr ⟨hw, hw'⟩⟩⟩⟩

theorem card_twoResidueCover_le {p : ℕ} (hp : 0 < p) (U : Finset ℤ)
    (start₁ len₁ start₂ len₂ : ℤ) (h₁ : 0 ≤ len₁) (h₂ : 0 ≤ len₂)
    (r₁ r₂ : ℤ → ZMod p) :
    ((twoResidueCover U start₁ len₁ start₂ len₂ r₁ r₂).card : ℝ) ≤
      (U.card : ℝ) * ((len₁ : ℝ) / p + 1) * ((len₂ : ℝ) / p + 1) := by
  classical
  let f := fun u : ℤ => ({u} : Finset ℤ).product
    ((residueSlice start₁ len₁ (r₁ u)).product (residueSlice start₂ len₂ (r₂ u)))
  have h : ((U.biUnion f).card : ℝ) ≤ ∑ u ∈ U, ((f u).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.card_biUnion_le : (U.biUnion f).card ≤ ∑ u ∈ U, (f u).card)
  calc
    _ ≤ ∑ u ∈ U, ((f u).card : ℝ) := h
    _ ≤ ∑ _u ∈ U, ((len₁ : ℝ) / p + 1) * ((len₂ : ℝ) / p + 1) := by
      apply Finset.sum_le_sum
      intro u _
      simp only [f, Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton,
        one_mul, Nat.cast_mul]
      exact mul_le_mul (card_residueSlice_le start₁ len₁ hp h₁ (r₁ u))
        (card_residueSlice_le start₂ len₂ hp h₂ (r₂ u)) (by positivity) (by positivity)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]

theorem sum_inverse_squares_tail_le (M : ℕ) (hM : 0 < M) (s : Finset ℕ)
    (hs : ∀ p ∈ s, M < p) :
    (∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
  let N := ∑ p ∈ s, p
  let g := fun n : ℕ => -(1 : ℝ) / ((n : ℝ) + (M : ℝ))
  have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hterm (p : ℕ) (hp : M < p) :
      (1 : ℝ) / (p : ℝ) ^ 2 ≤ g (p - (M + 1) + 1) - g (p - (M + 1)) := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hM.trans hp)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 :=
      sub_pos.mpr (by exact_mod_cast (show 1 < p by omega))
    have hcast : ((p - (M + 1) : ℕ) : ℝ) = (p : ℝ) - ((M + 1 : ℕ) : ℝ) :=
      Nat.cast_sub (by omega)
    simp only [g, Nat.cast_add, Nat.cast_one, hcast]
    have h1 : (p : ℝ) - ((M : ℝ) + 1) + (M : ℝ) = (p : ℝ) - 1 := by ring
    have h2 : (p : ℝ) - ((M : ℝ) + 1) + 1 + (M : ℝ) = (p : ℝ) := by ring
    rw [h1, h2]
    have hid : -(1 : ℝ) / (p : ℝ) - (-(1 : ℝ) / ((p : ℝ) - 1)) =
        1 / (((p : ℝ) - 1) * (p : ℝ)) := by
      field_simp [hp0.ne', hp1.ne'] <;> ring
    rw [hid]
    exact one_div_le_one_div_of_le (mul_pos hp1 hp0) (by nlinarith only [hp0])
  have hsub : s.image (fun p => p - (M + 1)) ⊆ Finset.range (N - M) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have hpN : p ≤ N := Finset.single_le_sum (fun q _ => Nat.zero_le q) hp
    have hpM := hs p hp
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun p : ℕ => p - (M + 1)) (s : Set ℕ) := by
    intro p hp q hq he
    change p - (M + 1) = q - (M + 1) at he
    have h₁ := hs p hp
    have h₂ := hs q hq
    omega
  calc
    _ ≤ ∑ p ∈ s, (g (p - (M + 1) + 1) - g (p - (M + 1))) :=
      Finset.sum_le_sum fun p hp => hterm p (hs p hp)
    _ = ∑ j ∈ s.image (fun p => p - (M + 1)), (g (j + 1) - g j) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ j ∈ Finset.range (N - M), (g (j + 1) - g j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      have hj : (0 : ℝ) < (j : ℝ) + (M : ℝ) := add_pos_of_nonneg_of_pos (by positivity) hMp
      have hmono : (1 : ℝ) / ((j : ℝ) + 1 + (M : ℝ)) ≤ 1 / ((j : ℝ) + (M : ℝ)) :=
        one_div_le_one_div_of_le hj (by linarith)
      simp only [g, Nat.cast_add, Nat.cast_one, neg_div]
      linarith
    _ = g (N - M) - g 0 := Finset.sum_range_sub _ _
    _ ≤ _ := by
      have hg0 : g 0 = -(1 : ℝ) / (M : ℝ) := by simp [g]
      have hgN : g (N - M) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      rw [hg0]
      calc
        _ ≤ 0 - (-(1 : ℝ) / (M : ℝ)) := sub_le_sub hgN le_rfl
        _ = _ := by ring

end Jsp000881
