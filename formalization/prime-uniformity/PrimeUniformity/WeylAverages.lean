module

public import PrimeUniformity.PhaseDetection
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Adapted from openai/math, `OAI/Combinatorics/SumProduct/Alignment/PolynomialWeyl01.lean`,
revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, under Apache-2.0.
The imports and namespace have been narrowed to the scalar recurrence proof.
-/

@[expose] public section

namespace PrimeUniformity

namespace WeylAverages
open scoped BigOperators ComplexConjugate
noncomputable section

def mean (N : ℕ) (f : ℕ → ℂ) : ℂ := 𝔼 x ∈ Finset.range N, f x

def derivative (a b : ℕ) (f : ℕ → ℂ) (x : ℕ) : ℂ :=
  f (x + a) * conj (f (x + b))

theorem norm_mean_le_one {N : ℕ} (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N f‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [mean, hN]
  · exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (Finset.nonempty_range_iff.mpr hN)
        (fun x _ => hf x))

theorem norm_derivative_le_one (a b : ℕ) (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∀ x, ‖derivative a b f x‖ ≤ 1 := by
  intro x
  simp only [derivative, norm_mul, RCLike.norm_conj]
  calc
    _ ≤ 1 * 1 := mul_le_mul (hf (x + a)) (hf (x + b)) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem norm_mean_shift_sub_le {N : ℕ} (hN : 0 < N) (h : ℕ) (f : ℕ → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N (fun x => f (x + h)) - mean N f‖ ≤ 2 * (h : ℝ) / N := by
  have hs : (∑ x ∈ Finset.range N, f (x + h)) - (∑ x ∈ Finset.range N, f x) =
      (∑ x ∈ Finset.range h, f (x + N)) - (∑ x ∈ Finset.range h, f x) := by
    have h₁ := Finset.sum_range_add f N h
    have h₂ := Finset.sum_range_add f h N
    rw [Nat.add_comm h N] at h₂
    have e₁ : (∑ x ∈ Finset.range h, f (N + x)) = ∑ x ∈ Finset.range h, f (x + N) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.add_comm N x]
    have e₂ : (∑ x ∈ Finset.range N, f (h + x)) = ∑ x ∈ Finset.range N, f (x + h) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.add_comm h x]
    rw [e₁] at h₁
    rw [e₂] at h₂
    linear_combination h₁ - h₂
  have hb (k : ℕ) : ‖∑ x ∈ Finset.range h, f (x + k)‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ x ∈ Finset.range h, ‖f (x + k)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ Finset.range h, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf (x + k))
      _ = _ := by simp
  have hb₀ : ‖∑ x ∈ Finset.range h, f x‖ ≤ (h : ℝ) := by simpa using hb 0
  rw [mean, mean, Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_range, ← sub_div, hs, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hN).le
  calc
    _ ≤ ‖∑ x ∈ Finset.range h, f (x + N)‖ + ‖∑ x ∈ Finset.range h, f x‖ := norm_sub_le _ _
    _ ≤ 2 * (h : ℝ) := by linarith [hb N]

theorem norm_expect_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖𝔼 i ∈ s, f i‖ ^ 2 ≤ 𝔼 i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · have h₁ := RCLike.norm_expect_le (K := ℂ) (s := s) (f := f)
    have h₂ := Finset.expect_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.expect_const hs] at h₂
    nlinarith [norm_nonneg (𝔼 i ∈ s, f i)]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem shift_average_error {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(𝔼 x ∈ Finset.range N, 𝔼 h ∈ Finset.range H, f (x + h)) - mean N f‖ ≤
      2 * (H : ℝ) / N := by
  rw [Finset.expect_comm]
  conv_lhs => rhs; rw [← Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)) (mean N f)]
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH))
  intro h hh
  apply (norm_mean_shift_sub_le hN h f hf).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have : (h : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hh).le
  linarith

theorem norm_expect_sq_eq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖𝔼 i ∈ s, f i‖ ^ 2 = (𝔼 a ∈ s, 𝔼 b ∈ s, f a * conj (f b)).re := by
  simp_rw [← Finset.mul_expect, ← map_expect (starRingEnd ℂ)]
  rw [← Finset.expect_mul, Complex.mul_conj]
  rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem van_der_corput {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N f‖ ^ 2 ≤
      (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H, ‖mean N (derivative a b f)‖) +
      4 * (H : ℝ) / N := by
  let z := 𝔼 x ∈ Finset.range N, 𝔼 h ∈ Finset.range H, f (x + h)
  have hz : ‖z‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
    intro x _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)) (fun h _ => hf (x + h))
  have hm := norm_mean_le_one f hf (N := N)
  have he := shift_average_error hN hH f hf
  have ht : ‖mean N f‖ - ‖z‖ ≤ 2 * (H : ℝ) / N := by
    have ht := norm_sub_norm_le (mean N f) z
    rw [norm_sub_rev] at ht
    exact ht.trans he
  have hs : ‖mean N f‖ ^ 2 ≤ ‖z‖ ^ 2 + 4 * (H : ℝ) / N := by
    have he₀ : 0 ≤ 2 * (H : ℝ) / N := by positivity
    have he₁ := mul_le_mul_of_nonneg_right ht (show 0 ≤ ‖mean N f‖ + ‖z‖ by positivity)
    have he₂ := mul_le_mul_of_nonneg_left (show ‖mean N f‖ + ‖z‖ ≤ 2 by linarith) he₀
    have hr : 2 * (H : ℝ) / N * 2 = 4 * H / N := by ring
    rw [hr] at he₂
    nlinarith
  apply hs.trans
  apply add_le_add _ le_rfl
  calc
    ‖z‖ ^ 2 ≤ 𝔼 x ∈ Finset.range N, ‖𝔼 h ∈ Finset.range H, f (x + h)‖ ^ 2 :=
      norm_expect_sq_le _ _
    _ = (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H,
        mean N (derivative a b f)).re := by
      simp only [norm_expect_sq_eq, ← Complex.re_expect]
      congr 1
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro a _
      rw [Finset.expect_comm]
      rfl
    _ ≤ _ := by
      rw [Complex.re_expect]
      apply Finset.expect_le_expect
      intro a _
      rw [Complex.re_expect]
      exact Finset.expect_le_expect (fun b _ => Complex.re_le_norm _)

noncomputable abbrev phase := recurrencePhase

@[simp] theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[simp] theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [recurrencePhase, mul_add, Complex.ofReal_add, Complex.exp_add, add_mul]

@[simp] theorem phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) :=
  recurrencePhase_sub x y

@[simp] theorem phase_nat_mul (x : ℝ) (n : ℕ) : phase ((n : ℝ) * x) = (phase x) ^ n := by
  simp only [phase, recurrencePhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def polynomialPhase (p : Polynomial ℝ) (x : ℕ) : ℂ := phase (p.eval (x : ℝ))

def polynomialDifference (a b : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.taylor (a : ℝ) p - Polynomial.taylor (b : ℝ) p

@[simp] theorem polynomialPhase_difference (a b : ℕ) (p : Polynomial ℝ) :
    polynomialPhase (polynomialDifference a b p) = derivative a b (polynomialPhase p) := by
  funext x
  simp [polynomialPhase, polynomialDifference, derivative, Polynomial.taylor_eval,
    Nat.cast_add]

theorem taylor_coeff_top (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (a : ℝ) :
    (Polynomial.taylor a p).coeff d = p.coeff d := by
  by_cases hd : p.natDegree = d
  · subst d
    exact Polynomial.coeff_taylor_natDegree a p
  · have hl : p.natDegree < d := lt_of_le_of_ne hp hd
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
      Polynomial.coeff_eq_zero_of_natDegree_lt]
    rwa [Polynomial.natDegree_taylor]

theorem polynomialDifference_degree (a b : ℕ) (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) :
    (polynomialDifference a b p).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp only [polynomialDifference, Polynomial.coeff_sub]
  by_cases he : n = d + 1
  · subst n
    rw [taylor_coeff_top p _ hp, taylor_coeff_top p _ hp, sub_self]
  · have hlt : p.natDegree < n := by omega
    have h₁ : (Polynomial.taylor (a : ℝ) p).natDegree < n := by
      rwa [Polynomial.natDegree_taylor]
    have h₂ : (Polynomial.taylor (b : ℝ) p).natDegree < n := by
      rwa [Polynomial.natDegree_taylor]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h₁,
      Polynomial.coeff_eq_zero_of_natDegree_lt h₂, sub_self]

theorem taylor_coeff_below_top (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d + 1) (a : ℝ) :
    (Polynomial.taylor a p).coeff d = p.coeff d + (d + 1 : ℕ) * p.coeff (d + 1) * a := by
  rw [Polynomial.taylor_coeff]
  have hdeg : ((Polynomial.hasseDeriv d) p).natDegree < 2 := by
    have h := Polynomial.natDegree_hasseDeriv_le p d
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Polynomial.hasseDeriv_coeff, Nat.choose_self, Nat.cast_one,
    one_mul, pow_zero, mul_one, pow_one]
  rw [Nat.add_comm 1 d, Nat.choose_succ_self_right]

theorem polynomialDifference_coeff (a b : ℕ) (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) :
    (polynomialDifference a b p).coeff d =
      (d + 1 : ℕ) * p.coeff (d + 1) * ((a : ℝ) - b) := by
  simp only [polynomialDifference, Polynomial.coeff_sub, taylor_coeff_below_top p d hp]
  ring

def linearBound (N : ℕ) (α : ℝ) : ℝ :=
  if phase α = 1 then 1 else min 1 (2 / ((N : ℝ) * ‖phase α - 1‖))

theorem norm_linear_mean_le {N : ℕ} (hN : 0 < N) (α β : ℝ) :
    ‖mean N (fun x => phase (α * x + β))‖ ≤ linearBound N α := by
  have hunit : ∀ x : ℕ, ‖phase (α * x + β)‖ ≤ 1 := by simp
  have h₁ := norm_mean_le_one _ hunit (N := N)
  unfold linearBound
  split_ifs with hα
  · exact h₁
  · apply le_min h₁
    have heq : mean N (fun x => phase (α * x + β)) =
        phase β * (∑ x ∈ Finset.range N, (phase α) ^ x) / (N : ℂ) := by
      simp only [mean, Finset.expect_eq_sum_div_card, Finset.card_range]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [phase_add, mul_comm α, phase_nat_mul, mul_comm]
    rw [heq, norm_div, norm_mul, norm_phase, one_mul, Complex.norm_natCast,
      geom_sum_eq hα, norm_div]
    have hb : ‖(phase α) ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖(phase α) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp only [norm_pow, norm_phase, one_pow, norm_one]; norm_num
    calc
      _ ≤ (2 / ‖phase α - 1‖) / N :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hb (norm_nonneg _))
          (Nat.cast_pos.mpr hN).le
      _ = _ := by ring

theorem exists_int_close_of_phase (α : ℝ) :
    ∃ m : ℤ, |α - m| ≤ ‖phase α - 1‖ / 4 := by
  let m : ℤ := ⌊α + 1 / 2⌋
  let t : ℝ := α - m
  have ht : |t| ≤ 1 / 2 := by
    apply abs_le.mpr
    have h₁ := Int.floor_le (α + 1 / 2)
    have h₂ := Int.lt_floor_add_one (α + 1 / 2)
    dsimp [t, m]
    constructor <;> linarith
  have he : phase t = phase α := by
    simp [t, recurrencePhase_int]
  have hnorm : ‖phase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    simp only [phase, recurrencePhase]
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [harg, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hbound
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hsim : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  rw [hsim] at hs
  refine ⟨m, ?_⟩
  change |t| ≤ _
  rw [← he, hnorm]
  linarith

theorem linear_inverse {N : ℕ} (hN : 0 < N) (α β δ : ℝ)
    (hδ : 0 < δ) (hlarge : δ ≤ ‖mean N (fun x => phase (α * x + β))‖) :
    ∃ m : ℤ, |α - m| ≤ 1 / (δ * N) := by
  obtain ⟨m, hm⟩ := exists_int_close_of_phase α
  refine ⟨m, hm.trans ?_⟩
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  by_cases hα : phase α = 1
  · simp only [hα, sub_self, norm_zero, zero_div]
    positivity
  · have hnorm : 0 < ‖phase α - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hα)
    have hl := norm_linear_mean_le hN α β
    simp only [linearBound, if_neg hα] at hl
    have hd : δ ≤ 2 / ((N : ℝ) * ‖phase α - 1‖) := hlarge.trans (hl.trans (min_le_right _ _))
    have hd' := (le_div_iff₀ (mul_pos hNp hnorm)).mp hd
    apply (le_div_iff₀ (mul_pos hδ hNp)).mpr
    nlinarith

end
end WeylAverages

end PrimeUniformity
