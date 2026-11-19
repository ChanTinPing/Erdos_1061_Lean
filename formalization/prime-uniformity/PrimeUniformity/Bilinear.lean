module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

private theorem norm_sum_mul_sq_le {I : Type*} (s : Finset I) (f g : I → ℂ) :
    ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * ∑ i ∈ s, ‖g i‖ ^ 2 := by
  have h := norm_sum_le s (fun i => f i * g i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖))

/-- Two applications of Cauchy–Schwarz remove the two separate coefficients
from a bilinear sum. The remaining term is a sum of squared column
correlations of the kernel. -/
theorem norm_bilinear_sum_pow_four_le {I J : Type*}
    (s : Finset I) (t : Finset J) (a : I → ℂ) (b : J → ℂ) (F : I → J → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * F i j‖ ^ 4 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) ^ 2 * (∑ j ∈ t, ‖b j‖ ^ 2) ^ 2 *
        ∑ j ∈ t, ∑ k ∈ t, ‖∑ i ∈ s, F i j * conj (F i k)‖ ^ 2 := by
  let row (i : I) := ∑ j ∈ t, b j * F i j
  let A := ∑ i ∈ s, ‖a i‖ ^ 2
  let B := ∑ j ∈ t, ‖b j‖ ^ 2
  let E := ∑ i ∈ s, ‖row i‖ ^ 2
  let R (j k : J) := ∑ i ∈ s, F i j * conj (F i k)
  let W (p : J × J) := b p.1 * conj (b p.2)
  let C (i : I) (j k : J) := (b j * conj (b k)) * (F i j * conj (F i k))
  have hrow (i : I) : ‖row i‖ ^ 2 = (∑ j ∈ t, ∑ k ∈ t, C i j k).re := by
    calc
      _ = (row i * conj (row i)).re := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := by
        congr 1
        simp only [row, map_sum]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, map_mul]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        dsimp [C]
        ac_rfl
  have hE : E = (∑ p ∈ t ×ˢ t, W p * R p.1 p.2).re := by
    simp only [E, hrow, ← Complex.re_sum]
    congr 1
    calc
      _ = ∑ j ∈ t, ∑ i ∈ s, ∑ k ∈ t, C i j k := Finset.sum_comm
      _ = ∑ j ∈ t, ∑ k ∈ t, ∑ i ∈ s, C i j k := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_product]
        simp only [W, R, C, Finset.mul_sum]
  have hW : (∑ p ∈ t ×ˢ t, ‖W p‖ ^ 2) = B ^ 2 := by
    rw [Finset.sum_product]
    simp only [W, norm_mul, Complex.norm_conj, mul_pow]
    rw [pow_two B]
    simp only [B, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
  have hsq : E ^ 2 ≤ B ^ 2 * ∑ j ∈ t, ∑ k ∈ t, ‖R j k‖ ^ 2 := by
    have h := norm_sum_mul_sq_le (t ×ˢ t) W (fun p => R p.1 p.2)
    rw [hW] at h
    have hnonneg : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa only [Finset.sum_product] using
      (pow_le_pow_left₀ hnonneg (hE.trans_le (Complex.re_le_norm _)) 2).trans h
  have hfirst : ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * F i j‖ ^ 2 ≤ A * E := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    exact norm_sum_mul_sq_le s a row
  calc
    _ = (‖∑ i ∈ s, ∑ j ∈ t, a i * b j * F i j‖ ^ 2) ^ 2 := by rw [← pow_mul]
    _ ≤ (A * E) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ = A ^ 2 * E ^ 2 := mul_pow _ _ _
    _ ≤ A ^ 2 * (B ^ 2 * ∑ j ∈ t, ∑ k ∈ t, ‖R j k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by simp only [A, B, R, mul_assoc]

/-- Extend the one-variable input by zero before forming the bilinear kernel.
The product cutoffs apply to each corner of the resulting column correlation. -/
def typeIIKernel (L X : ℕ) (f : ℕ → ℂ) (i j : ℕ) : ℂ :=
  if L ≤ i * j ∧ i * j ≤ X then f (i * j) else 0

/-- The finite Type II estimate with a lower and upper cutoff on the product. -/
theorem norm_typeII_sum_pow_four_le (s t : Finset ℕ) (a b f : ℕ → ℂ) (L X : ℕ) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * typeIIKernel L X f i j‖ ^ 4 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) ^ 2 * (∑ j ∈ t, ‖b j‖ ^ 2) ^ 2 *
        ∑ j ∈ t, ∑ k ∈ t,
          ‖∑ i ∈ s, typeIIKernel L X f i j * conj (typeIIKernel L X f i k)‖ ^ 2 :=
  norm_bilinear_sum_pow_four_le s t a b (typeIIKernel L X f)

/-- A lower bound for the sum of squared column correlations of a one-bounded
kernel gives a positive density of pairs with large correlation. -/
theorem dense_large_column_correlations {I J : Type*} (s : Finset I) (t : Finset J)
    (hs : s.Nonempty) (F : I → J → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ i ∈ s, ∀ j ∈ t, ‖F i j‖ ≤ 1)
    (hlower : δ * (s.card : ℝ) ^ 2 * (t.card : ℝ) ^ 2 ≤
      ∑ j ∈ t, ∑ k ∈ t, ‖∑ i ∈ s, F i j * conj (F i k)‖ ^ 2) :
    (δ / 2) * (t.card : ℝ) ^ 2 ≤
      (((t ×ˢ t).filter (fun p : J × J =>
        (δ / 2) * (s.card : ℝ) ≤ ‖∑ i ∈ s, F i p.1 * conj (F i p.2)‖)).card : ℝ) := by
  classical
  let U := t ×ˢ t
  let R (p : J × J) := ‖∑ i ∈ s, F i p.1 * conj (F i p.2)‖
  let good (p : J × J) := (δ / 2) * (s.card : ℝ) ≤ R p
  have hR (p : J × J) (hp : p ∈ U) : R p ≤ (s.card : ℝ) := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    calc
      _ ≤ ∑ i ∈ s, ‖F i p.1 * conj (F i p.2)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (hF i hi _ h₁) (norm_nonneg _) (hF i hi _ h₂)
      _ = _ := by simp
  have hpoint (p : J × J) (hp : p ∈ U) :
      R p ^ 2 ≤ (s.card : ℝ) ^ 2 * (δ / 2 + if good p then 1 else 0) := by
    have hr := hR p hp
    have hr0 : 0 ≤ R p := norm_nonneg _
    by_cases hg : good p
    · rw [if_pos hg]
      exact (pow_le_pow_left₀ hr0 hr 2).trans (le_mul_of_one_le_right (sq_nonneg _)
        (by linarith))
    · rw [if_neg hg, add_zero]
      have hrδ : R p ≤ (δ / 2) * (s.card : ℝ) := (lt_of_not_ge hg).le
      calc
        R p ^ 2 = R p * R p := pow_two _
        _ ≤ ((δ / 2) * (s.card : ℝ)) * (s.card : ℝ) :=
          mul_le_mul hrδ hr hr0 (by positivity)
        _ = _ := by ring
  have hsum : δ * (s.card : ℝ) ^ 2 * (t.card : ℝ) ^ 2 ≤ ∑ p ∈ U, R p ^ 2 := by
    simpa only [U, R, Finset.sum_product] using hlower
  have hupper := hsum.trans (Finset.sum_le_sum hpoint)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_filter] at hupper
  have hcard : (U.card : ℝ) = (t.card : ℝ) ^ 2 := by
    simp only [U, Finset.card_product, Nat.cast_mul, pow_two]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hupper
  have hspos : 0 < (s.card : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hs.card_pos) _
  have hcancel : δ * (t.card : ℝ) ^ 2 ≤ (t.card : ℝ) ^ 2 * (δ / 2) + ((U.filter good).card : ℝ) :=
    (mul_le_mul_iff_right₀ hspos).mp (by
      calc
        _ = δ * (s.card : ℝ) ^ 2 * (t.card : ℝ) ^ 2 := by ring
        _ ≤ _ := hupper)
  change _ ≤ ((U.filter good).card : ℝ)
  linarith

end PrimeUniformity
