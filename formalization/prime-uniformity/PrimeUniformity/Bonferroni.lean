module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

noncomputable def survivingWeight {ι α : Type*} (I : Finset ι) (X : Finset α)
    (bad : ι → α → Prop) (w : α → ℝ) : ℝ := by
  classical
  exact ∑ x ∈ X with ∀ i ∈ I, ¬ bad i x, w x

noncomputable def intersectionWeight {ι α : Type*} (J : Finset ι) (X : Finset α)
    (bad : ι → α → Prop) (w : α → ℝ) : ℝ := by
  classical
  exact ∑ x ∈ X with ∀ i ∈ J, bad i x, w x

noncomputable def truncation {ι α : Type*} (I : Finset ι) (X : Finset α)
    (bad : ι → α → Prop) (w : α → ℝ) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j *
    ∑ J ∈ I.powersetCard j, intersectionWeight J X bad w

private noncomputable def binomialTruncation (n L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ)

private noncomputable def badIndices {ι α : Type*} (I : Finset ι) (bad : ι → α → Prop)
    (x : α) : Finset ι := by
  classical exact I.filter fun i => bad i x

private theorem binomialTruncation_zero (L : ℕ) : binomialTruncation 0 L = 1 := by
  simp [binomialTruncation, Finset.sum_range_succ', Nat.choose_eq_zero_of_lt]

private theorem binomialTruncation_succ (n L : ℕ) :
    binomialTruncation (n + 1) L = (-1 : ℝ) ^ L * (n.choose L : ℝ) := by
  unfold binomialTruncation
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := L))

private noncomputable def subsetsAllBad {ι α : Type*} (I : Finset ι) (bad : ι → α → Prop)
    (x : α) (j : ℕ) : Finset (Finset ι) := by
  classical
  exact (I.powersetCard j).filter fun J => ∀ i ∈ J, bad i x

private theorem count_subset_badIndices {ι α : Type*} (I : Finset ι) (bad : ι → α → Prop)
    (x : α) (j : ℕ) :
    (subsetsAllBad I bad x j).card = (badIndices I bad x).card.choose j := by
  classical
  have h : subsetsAllBad I bad x j = (badIndices I bad x).powersetCard j := by
    ext J
    simp only [subsetsAllBad, badIndices, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨fun i hi => Finset.mem_filter.mpr ⟨h₁ hi, h₃ i hi⟩, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨fun i hi => (Finset.mem_filter.mp (h₁ hi)).1, h₂⟩,
        fun i hi => (Finset.mem_filter.mp (h₁ hi)).2⟩
  rw [h, Finset.card_powersetCard]

private theorem truncation_eq_sum {ι α : Type*} (I : Finset ι) (X : Finset α)
    (bad : ι → α → Prop) (w : α → ℝ) (L : ℕ) :
    truncation I X bad w L =
      ∑ x ∈ X, w x * binomialTruncation (badIndices I bad x).card L := by
  classical
  unfold truncation intersectionWeight binomialTruncation
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  have hterm (x : α) (j : ℕ) :
      ∑ J ∈ I.powersetCard j, (-1 : ℝ) ^ j * (if ∀ i ∈ J, bad i x then w x else 0) =
        w x * ((-1 : ℝ) ^ j * ((badIndices I bad x).card.choose j : ℝ)) := by
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    change (-1 : ℝ) ^ j * (∑ _J ∈ subsetsAllBad I bad x j, w x) = _
    rw [Finset.sum_const, nsmul_eq_mul, count_subset_badIndices] <;> ring
  calc
    _ = ∑ j ∈ Finset.range (L + 1), ∑ x ∈ X, ∑ J ∈ I.powersetCard j,
        (-1 : ℝ) ^ j * (if ∀ i ∈ J, bad i x then w x else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ x ∈ X, ∑ j ∈ Finset.range (L + 1), ∑ J ∈ I.powersetCard j,
        (-1 : ℝ) ^ j * (if ∀ i ∈ J, bad i x then w x else 0) := Finset.sum_comm
    _ = _ := by simp_rw [hterm]

private theorem badIndices_card_eq_zero_iff {ι α : Type*}
    (I : Finset ι) (bad : ι → α → Prop) (x : α) :
    (badIndices I bad x).card = 0 ↔ ∀ i ∈ I, ¬ bad i x := by
  classical
  simp [badIndices, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- Odd truncations give lower bounds and even truncations give upper bounds,
also for nonnegative weights. -/
theorem bonferroni {ι α : Type*} (I : Finset ι) (X : Finset α)
    (bad : ι → α → Prop) (w : α → ℝ) (hw : ∀ x ∈ X, 0 ≤ w x)
    (L : ℕ) (hL : Odd L) :
    truncation I X bad w L ≤ survivingWeight I X bad w ∧
      survivingWeight I X bad w ≤ truncation I X bad w (L + 1) := by
  classical
  have hsign : Even (L + 1) := hL.add_odd odd_one
  have hpoint (n : ℕ) :
      binomialTruncation n L ≤ (if n = 0 then 1 else 0 : ℝ) ∧
        (if n = 0 then 1 else 0 : ℝ) ≤ binomialTruncation n (L + 1) := by
    cases n with
    | zero => simp [binomialTruncation_zero]
    | succ n =>
      rw [binomialTruncation_succ, binomialTruncation_succ, hL.neg_one_pow, hsign.neg_one_pow]
      simp
  have hsurv : survivingWeight I X bad w =
      ∑ x ∈ X, w x * (if (badIndices I bad x).card = 0 then 1 else 0 : ℝ) := by
    unfold survivingWeight
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    have hcard := badIndices_card_eq_zero_iff I bad x
    by_cases hx : ∀ i ∈ I, ¬ bad i x
    · rw [if_pos hx, if_pos (hcard.mpr hx), mul_one]
    · rw [if_neg hx, if_neg (mt hcard.mp hx), mul_zero]
  rw [truncation_eq_sum, truncation_eq_sum, hsurv]
  exact ⟨Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hpoint _).1 (hw x hx),
    Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hpoint _).2 (hw x hx)⟩

end PrimeUniformity
