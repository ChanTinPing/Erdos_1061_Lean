module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators Polynomial
open Polynomial

/-- An inverse affine substitution with integral shift and dilation in a
degree-`k` integer polynomial has a common denominator dividing `b^k`. -/
theorem exists_integer_polynomial_clear_inverse_affine
    {K : Type*} [Field K] [CharZero K] (P : ℤ[X]) (k : ℕ) (hP : P.natDegree ≤ k)
    (a b : ℤ) (hb : b ≠ 0) :
    ∃ R : ℤ[X], ∀ x : K,
      (R.map (Int.castRingHom K)).eval x =
        (b : K) ^ k * (P.map (Int.castRingHom K)).eval ((x - (a : K)) / (b : K)) := by
  let R : ℤ[X] :=
    ∑ i ∈ Finset.range (k + 1), C (P.coeff i * b ^ (k - i)) * (X - C a) ^ i
  refine ⟨R, ?_⟩
  intro x
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  have heval (y : K) :
      (P.map (Int.castRingHom K)).eval y =
        ∑ i ∈ Finset.range (k + 1), ((P.coeff i : ℤ) : K) * y ^ i := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Int.coe_castRingHom]
  rw [heval, Finset.mul_sum]
  simp only [R, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
    RingHom.map_mul, RingHom.map_pow, Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [div_pow]
  simp only [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero i hbK)).mpr
  calc
    _ = (b : K) ^ (k - i + i) * (↑(P.coeff i) * (x - (a : K)) ^ i) := by
      rw [pow_add]
      ring
    _ = _ := by rw [Nat.sub_add_cancel hi']

/-- Undo an integral shift and dilation while preserving the scale of the
coefficient errors. Multiplication by `b^k` clears the rational denominator. -/
theorem exists_integer_approx_clear_inverse_affine
    (p : ℝ[X]) (Q : ℤ[X]) (k : ℕ) (hp : p.natDegree ≤ k) (hQ : Q.natDegree ≤ k)
    (a b : ℤ) (hb : b ≠ 0) {S B H : ℝ} (hS : 0 < S) (hB : 1 ≤ B) (hH : 0 ≤ H)
    (ha : |(a : ℝ)| ≤ B * S) (hbB : |(b : ℝ)| ≤ B)
    (herror : ∀ i ≤ k, |(p.comp (C (a : ℝ) + C (b : ℝ) * X)).coeff i -
        ((Q.coeff i : ℤ) : ℝ)| ≤ H / S ^ i) :
    ∃ R : ℤ[X], ∀ j ≤ k, |(b : ℝ) ^ k * p.coeff j - ((R.coeff j : ℤ) : ℝ)| ≤
      (k + 1 : ℕ) * (2 : ℝ) ^ k * B ^ k * H / S ^ j := by
  let E := p.comp (C (a : ℝ) + C (b : ℝ) * X) - Q.map (Int.castRingHom ℝ)
  have hcomp : (p.comp (C (a : ℝ) + C (b : ℝ) * X)).natDegree ≤ k := by
    have haff : (C (a : ℝ) + C (b : ℝ) * X).natDegree ≤ 1 := by
      apply (natDegree_add_le _ _).trans
      refine max_le (by simp) ?_
      exact (natDegree_mul_le.trans (by simp))
    exact (natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hp haff))
  have hE : E.natDegree ≤ k := (natDegree_sub_le _ _).trans
    (max_le hcomp (natDegree_map_le.trans hQ))
  have herr (i : ℕ) (hi : i ≤ k) : |E.coeff i| ≤ H / S ^ i := by
    simpa only [E, coeff_sub, coeff_map, Int.coe_castRingHom] using herror i hi
  obtain ⟨R, hR⟩ := exists_integer_polynomial_clear_inverse_affine (K := ℝ) Q k hQ a b hb
  refine ⟨R, fun j hj => ?_⟩
  let F : ℝ[X] := ∑ i ∈ Finset.range (k + 1),
    C (E.coeff i * (b : ℝ) ^ (k - i)) * (X + C (-(a : ℝ))) ^ i
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hF : C ((b : ℝ) ^ k) * p - R.map (Int.castRingHom ℝ) = F := by
    let _ : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    have heval (y : ℝ) : E.eval y = ∑ i ∈ Finset.range (k + 1), E.coeff i * y ^ i :=
      eval_eq_sum_range' (Nat.lt_succ_of_le hE) y
    have hFE : F.eval x = (b : ℝ) ^ k * E.eval ((x - (a : ℝ)) / (b : ℝ)) := by
      rw [heval, Finset.mul_sum]
      simp only [F, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X, ← sub_eq_add_neg]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [div_pow]
      simp only [← mul_div_assoc]
      apply (eq_div_iff (pow_ne_zero i hbR)).mpr
      rw [show (b : ℝ) ^ k = (b : ℝ) ^ (k - i) * (b : ℝ) ^ i by
        rw [← pow_add, Nat.sub_add_cancel hi']]
      ring
    rw [eval_sub, eval_mul, eval_C, hR x, hFE]
    simp only [E, eval_sub, eval_comp, eval_add, eval_C, eval_mul, eval_X]
    rw [mul_div_cancel₀ _ hbR, add_sub_cancel]
    ring
  have hcoeff := congrArg (fun f : ℝ[X] => f.coeff j) hF
  simp only [coeff_sub, coeff_C_mul, coeff_map, Int.coe_castRingHom] at hcoeff
  rw [hcoeff]
  simp only [F, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        |E.coeff i * (b : ℝ) ^ (k - i) * ((-(a : ℝ)) ^ (i - j) * (i.choose j : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (k + 1), (2 : ℝ) ^ k * B ^ k * H / S ^ j := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases hij : j ≤ i
      · simp only [abs_mul, abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg (i.choose j) : 0 ≤ (i.choose j : ℝ))]
        have hchoose : (i.choose j : ℝ) ≤ (2 : ℝ) ^ k := by
          exact_mod_cast (Nat.choose_le_two_pow i j).trans
            (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hi')
        calc
          _ ≤ (H / S ^ i) * B ^ (k - i) * ((B * S) ^ (i - j) * (2 : ℝ) ^ k) := by
            gcongr <;> first | exact herr i hi' | exact hbB | exact ha | exact hchoose
          _ = (2 : ℝ) ^ k * B ^ (k - j) * H / S ^ j := by
            have hBexp : k - i + (i - j) = k - j := by omega
            rw [mul_pow, show S ^ i = S ^ (i - j) * S ^ j by rw [← pow_add, Nat.sub_add_cancel hij],
              show B ^ (k - j) = B ^ (k - i) * B ^ (i - j) by rw [← pow_add, hBexp]]
            field_simp [hS.ne']
            <;> ring
          _ ≤ _ := by
            gcongr
            exact Nat.sub_le _ _
      · simp only [Nat.choose_eq_zero_of_lt (lt_of_not_ge hij), Nat.cast_zero, mul_zero, abs_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end PrimeUniformity
