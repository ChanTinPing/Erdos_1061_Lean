module

public import PrimeUniformity.Bonferroni
public import PrimeUniformity.CramerBudget
import Mathlib.Tactic.Linarith

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

noncomputable def independentTruncation (P : Finset ℕ) (g : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j *
    ∑ J ∈ P.powersetCard j, ∏ p ∈ J, g p

private noncomputable def bernoulliWeight (P : Finset ℕ) (g : ℕ → ℝ) (J : Finset ℕ) : ℝ :=
  (∏ p ∈ J, g p) * ∏ p ∈ P \ J, (1 - g p)

private theorem bernoulli_intersection (P J : Finset ℕ) (hJ : J ⊆ P) (g : ℕ → ℝ) :
    intersectionWeight J P.powerset (fun p S => p ∈ S) (bernoulliWeight P g) =
      ∏ p ∈ J, g p := by
  classical
  have hmem (S : Finset ℕ) : (S ∈ P.powerset ∧ ∀ p ∈ J, p ∈ S) ↔
      S ∈ (P \ J).powerset.image (fun U => U ∪ J) := by
    rw [Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hSP, hJS⟩
      refine ⟨S \ J, Finset.mem_powerset.mpr ?_, Finset.sdiff_union_of_subset hJS⟩
      intro p hp
      obtain ⟨hpS, hpJ⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨hSP hpS, hpJ⟩
    · rintro ⟨U, hU, rfl⟩
      have hu := Finset.mem_powerset.mp hU
      exact ⟨Finset.union_subset (hu.trans Finset.sdiff_subset) hJ,
        fun _ hp => Finset.mem_union_right _ hp⟩
  have hdis (U : Finset ℕ) (hU : U ∈ (P \ J).powerset) : Disjoint U J := by
    apply Finset.disjoint_left.mpr
    intro p hpU hpJ
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hpU)).2 hpJ
  have hinj : (↑(P \ J).powerset : Set (Finset ℕ)).InjOn (fun U => U ∪ J) := by
    intro U hU V hV h
    have h' := congrArg (fun F : Finset ℕ => F \ J) h
    simpa only [Finset.union_sdiff_cancel_right (hdis U hU),
      Finset.union_sdiff_cancel_right (hdis V hV)] using h'
  unfold intersectionWeight
  have hs (U : Finset ℕ) : P \ (U ∪ J) = (P \ J) \ U := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  calc
    _ = ∑ S ∈ (P \ J).powerset.image (fun U => U ∪ J), bernoulliWeight P g S := by
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext S
      simpa only [Finset.mem_filter] using hmem S
    _ = ∑ U ∈ (P \ J).powerset, bernoulliWeight P g (U ∪ J) := Finset.sum_image hinj
    _ = ∑ U ∈ (P \ J).powerset, (∏ p ∈ J, g p) * bernoulliWeight (P \ J) g U := by
      apply Finset.sum_congr rfl
      intro U hU
      unfold bernoulliWeight
      rw [Finset.prod_union (hdis U hU), hs]
      ring
    _ = (∏ p ∈ J, g p) * (∏ p ∈ P \ J, (g p + (1 - g p))) := by
      rw [Finset.prod_add g (fun p => 1 - g p) (P \ J), Finset.mul_sum] <;> rfl
    _ = _ := by
      simp only [show ∀ a : ℝ, a + (1 - a) = 1 from fun a => by ring,
        Finset.prod_const_one, mul_one]

private theorem bernoulli_survival (P : Finset ℕ) (g : ℕ → ℝ) :
    survivingWeight P P.powerset (fun p S => p ∈ S) (bernoulliWeight P g) =
      ∏ p ∈ P, (1 - g p) := by
  classical
  have hset : P.powerset.filter (fun S => ∀ p ∈ P, p ∉ S) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, h⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun p hp => h p (hS hp) hp
    · rintro rfl
      simp
  unfold survivingWeight
  rw [hset]
  simp [bernoulliWeight]

/-- Odd and even independent truncations bracket the product of survival probabilities. -/
theorem independentTruncation_bounds (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) (L : ℕ) (hL : Odd L) :
    independentTruncation P g L ≤ (∏ p ∈ P, (1 - g p)) ∧
      (∏ p ∈ P, (1 - g p)) ≤ independentTruncation P g (L + 1) := by
  classical
  have hw (J : Finset ℕ) (hJ : J ∈ P.powerset) : 0 ≤ bernoulliWeight P g J := by
    apply mul_nonneg
    · exact Finset.prod_nonneg fun p hp => (hg p ((Finset.mem_powerset.mp hJ) hp)).1
    · exact Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hg p (Finset.mem_sdiff.mp hp).1).2
  have he (n : ℕ) : truncation P P.powerset (fun p S => p ∈ S) (bernoulliWeight P g) n =
      independentTruncation P g n := by
    unfold truncation independentTruncation
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact Finset.sum_congr rfl fun J hJ => bernoulli_intersection P J (Finset.mem_powersetCard.mp hJ).1 g
  simpa only [bernoulli_survival, he] using
    bonferroni P P.powerset (fun p S => p ∈ S) (bernoulliWeight P g) hw L hL

private theorem independentTruncation_succ (P : Finset ℕ) (g : ℕ → ℝ) (L : ℕ) (hL : Odd L) :
    independentTruncation P g (L + 1) =
      independentTruncation P g L + (∑ J ∈ P.powersetCard (L + 1), ∏ p ∈ J, g p) := by
  unfold independentTruncation
  rw [Finset.sum_range_succ, hL.add_one.neg_one_pow, one_mul]

/-- The omitted first even term upper bounds the gap between the exact
independent survival probability and its odd truncation. -/
theorem independentTruncation_ge_product_sub_tail (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) (L : ℕ) (hL : Odd L) :
    (∏ p ∈ P, (1 - g p)) -
        (∑ J ∈ P.powersetCard (L + 1), ∏ p ∈ J, g p) ≤ independentTruncation P g L := by
  have hbound := (independentTruncation_bounds P g hg L hL).2
  rw [independentTruncation_succ P g L hL] at hbound
  linarith only [hbound]

/-- Two Bonferroni truncations compare actual survival to independent survival.
The errors of the intersection estimates are charged only to subsets used by the
larger truncation. -/
theorem survivingWeight_error {α : Type*}
    (P : Finset ℕ) (X : Finset α) (bad : ℕ → α → Prop) (w : α → ℝ)
    (hw : ∀ x ∈ X, 0 ≤ w x) (g : ℕ → ℝ) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (err : Finset ℕ → ℝ)
    (herr : ∀ J ⊆ P, 0 ≤ err J) (L : ℕ) (hL : Odd L)
    (hinter : ∀ J ⊆ P,
      |intersectionWeight J X bad w - M * (∏ p ∈ J, g p)| ≤ err J) :
    |survivingWeight P X bad w - M * (∏ p ∈ P, (1 - g p))| ≤
      (∑ j ∈ Finset.range (L + 2), ∑ J ∈ P.powersetCard j, err J) +
        M * ((∑ p ∈ P, g p) ^ (L + 1) / ((L + 1).factorial : ℝ)) := by
  let E (n : ℕ) := ∑ j ∈ Finset.range (n + 1), ∑ J ∈ P.powersetCard j, err J
  have htrunc (n : ℕ) : |truncation P X bad w n - M * independentTruncation P g n| ≤ E n := by
    unfold truncation independentTruncation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [mul_left_comm M, ← mul_sub, abs_mul]
    simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun J hJ => hinter J (Finset.mem_powersetCard.mp hJ).1
  have hE : E L ≤ E (L + 1) := by
    simp only [E, Finset.sum_range_succ (n := L + 1)]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun J hJ => herr J (Finset.mem_powersetCard.mp hJ).1)
  let prod := ∏ p ∈ P, (1 - g p)
  let tail := (∑ p ∈ P, g p) ^ (L + 1) / ((L + 1).factorial : ℝ)
  have hs := independentTruncation_bounds P g hg L hL
  have ha := bonferroni P X bad w hw L hL
  have ht := sum_powersetCard_prod_le_pow_div_factorial P g (fun p hp => (hg p hp).1) (L + 1)
  have hlo : prod - tail ≤ independentTruncation P g L :=
    (sub_le_sub_left ht _).trans (independentTruncation_ge_product_sub_tail P g hg L hL)
  have hhi : independentTruncation P g (L + 1) ≤ prod + tail := by
    rw [independentTruncation_succ P g L hL]
    exact add_le_add hs.1 ht
  have h₁ := (abs_le.mp ((htrunc L).trans hE)).1
  have h₂ := (abs_le.mp (htrunc (L + 1))).2
  have hloM := mul_le_mul_of_nonneg_left hlo hM
  have hhiM := mul_le_mul_of_nonneg_left hhi hM
  change |survivingWeight P X bad w - M * prod| ≤ E (L + 1) + M * tail
  rw [abs_le]
  constructor <;> linarith only [ha.1, ha.2, h₁, h₂, hloM, hhiM]

end PrimeUniformity
