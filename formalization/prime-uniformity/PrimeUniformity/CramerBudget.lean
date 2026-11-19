module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The elementary symmetric bound for the sieve truncation error

The first omitted term in the odd Bonferroni truncation is bounded by
the corresponding exponential series term. This needs only finite sums
and products of the local bad densities.
-/

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

private noncomputable def symmetricWeight {ι : Type*} (P : Finset ι) (g : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ J ∈ P.powersetCard r, ∏ p ∈ J, g p

private theorem symmetricWeight_insert_succ {ι : Type*} [DecidableEq ι]
    {P : Finset ι} {a : ι} (ha : a ∉ P) (g : ι → ℝ) (r : ℕ) :
    symmetricWeight (insert a P) g (r + 1) =
      symmetricWeight P g (r + 1) + g a * symmetricWeight P g r := by
  have havoid {J : Finset ι} {k : ℕ} (hJ : J ∈ P.powersetCard k) : a ∉ J :=
    fun h => ha ((Finset.mem_powersetCard.mp hJ).1 h)
  have hdis : Disjoint (P.powersetCard (r + 1)) ((P.powersetCard r).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro J hJ he
    obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp he
    exact havoid hJ (Finset.mem_insert_self a K)
  have hinj : Set.InjOn (insert a) (P.powersetCard r : Set (Finset ι)) := by
    intro J hJ K hK h
    ext b
    have hb : b ∈ insert a J ↔ b ∈ insert a K := by rw [h]
    by_cases he : b = a
    · subst b
      simp only [havoid hJ, havoid hK]
    · simpa only [Finset.mem_insert, he, false_or] using hb
  unfold symmetricWeight
  rw [Finset.powersetCard_succ_insert ha r, Finset.sum_union hdis, Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.prod_insert (havoid hJ)]

private theorem pow_add_ge_two_terms {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (r : ℕ) :
    u ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * v * u ^ r ≤ (u + v) ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : u ^ (r + 1) ≤ (u + v) ^ (r + 1) :=
      pow_le_pow_left₀ hu (le_add_of_nonneg_right hv) _
    calc
      _ = u * (u ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * v * u ^ r) + v * u ^ (r + 1) := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ ≤ u * (u + v) ^ (r + 1) + v * (u + v) ^ (r + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left ih hu) (mul_le_mul_of_nonneg_left hp hv)
      _ = _ := by
        simp only [pow_succ]
        ring

private theorem factorial_mul_symmetricWeight_le {ι : Type*} (P : Finset ι) (g : ι → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) : ∀ r : ℕ,
    (r.factorial : ℝ) * symmetricWeight P g r ≤ (∑ p ∈ P, g p) ^ r := by
  classical
  revert hg
  induction P using Finset.induction_on with
  | empty =>
    intro _ r
    cases r with
    | zero => simp [symmetricWeight]
    | succ r =>
      have hP : (∅ : Finset ι).powersetCard (r + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [symmetricWeight, hP]
  | @insert a P ha ih =>
    intro hg r
    cases r with
    | zero => simp [symmetricWeight]
    | succ r =>
      let u : ℝ := ∑ p ∈ P, g p
      have hgP : ∀ p ∈ P, 0 ≤ g p := fun p hp => hg p (Finset.mem_insert_of_mem hp)
      have hu : 0 ≤ u := Finset.sum_nonneg hgP
      have hva : 0 ≤ g a := hg a (Finset.mem_insert_self a P)
      have hmul : 0 ≤ ((r + 1 : ℕ) : ℝ) * g a := mul_nonneg (Nat.cast_nonneg _) hva
      rw [symmetricWeight_insert_succ ha g r, Finset.sum_insert ha]
      calc
        _ = ((r + 1).factorial : ℝ) * symmetricWeight P g (r + 1) +
            ((r + 1 : ℕ) : ℝ) * g a * ((r.factorial : ℝ) * symmetricWeight P g r) := by
          simp only [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ u ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * g a * u ^ r :=
          add_le_add (ih hgP (r + 1)) (mul_le_mul_of_nonneg_left (ih hgP r) hmul)
        _ ≤ (u + g a) ^ (r + 1) := pow_add_ge_two_terms hu hva r
        _ = _ := by rw [add_comm u (g a)]

/-- Bound the first omitted even term in the odd truncation, using only
the sum of the local bad densities. -/
theorem sum_powersetCard_prod_le_pow_div_factorial {ι : Type*} (P : Finset ι) (g : ι → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) (r : ℕ) :
    (∑ J ∈ P.powersetCard r, ∏ p ∈ J, g p) ≤
      (∑ p ∈ P, g p) ^ r / (r.factorial : ℝ) := by
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  apply (le_div_iff₀ hfac).mpr
  simpa only [symmetricWeight, mul_comm (r.factorial : ℝ)] using factorial_mul_symmetricWeight_le P g hg r

end PrimeUniformity
