module

public import PrimeUniformity.AffinePolynomial
public import PrimeUniformity.DyadicDilation
import PrimeUniformity.LogSavings
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Classical Polynomial
open Polynomial

/-- The Weyl inverse budgets through a fixed degree are exponential in
the same logarithmic scale as the reciprocal-correlation cutoff. -/
theorem exists_uniform_leadingInverseBudget_exp_bound (s : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ k ≤ s, ∀ {p : ℝ}, 1 ≤ p → ∀ R : ℕ,
      (R : ℝ) ≤ Real.exp p → (WeylInverse.leadingInverseBudget k R : ℝ) ≤ Real.exp ((C : ℝ) * p) := by
  choose Q hQ using WeylInverse.leadingInverseBudget_polynomial
  let B (k : ℕ) := (Q k).eval 1 + (Q k).natDegree
  let C := 1 + ∑ k ∈ Finset.range (s + 1), B k
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro k hk p hp R hR
  have hBk : B k ≤ C := by
    have hsum := Finset.single_le_sum (f := B) (fun i _ => Nat.zero_le (B i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp only [C]
    exact hsum.trans (Nat.le_add_left _ _)
  calc
    _ = (↑((Q k).eval R) : ℝ) := by rw [hQ]
    _ ≤ Real.exp (↑((Q k).eval 1) + ((Q k).natDegree : ℝ) * p) :=
      natPolynomial_eval_le_exp (Q k) R (zero_le_one.trans hp) hR
    _ ≤ Real.exp ((B k : ℝ) * p) := by
      apply Real.exp_le_exp.mpr
      simp only [B, Nat.cast_add, add_mul]
      exact add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg _) hp) le_rfl
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hBk) (zero_le_one.trans hp))

/-- Clear the affine denominator with only positive-degree coefficient constraints.
The constant term can always be rounded within the error budget. -/
theorem exists_integer_approx_clear_inverse_affine_positive
    (p : ℝ[X]) (K : ℕ) (hp : p.natDegree ≤ K)
    (a b : ℤ) (hb : b ≠ 0) {S B H : ℝ} (hS : 0 < S) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (ha : |(a : ℝ)| ≤ B * S) (hbB : |(b : ℝ)| ≤ B)
    (herror : ∀ j, 0 < j → j ≤ K → ∃ z : ℤ,
      |(p.comp (C (a : ℝ) + C (b : ℝ) * X)).coeff j - (z : ℝ)| ≤ H / S ^ j) :
    ∀ j, 0 < j → j ≤ K → ∃ z : ℤ, |(b : ℝ) ^ K * p.coeff j - z| ≤
      (K + 1 : ℕ) * (2 : ℝ) ^ K * B ^ K * H / S ^ j := by
  let u := p.comp (C (a : ℝ) + C (b : ℝ) * X)
  have hex (j : ℕ) (hj : j ≤ K) : ∃ z : ℤ, |u.coeff j - z| ≤ H / S ^ j := by
    by_cases hj0 : j = 0
    · subst j
      refine ⟨⌊u.coeff 0⌋, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _)), pow_zero, div_one]
      linarith only [Int.lt_floor_add_one (u.coeff 0), hH]
    · exact herror j (Nat.pos_of_ne_zero hj0) hj
  let z (j : ℕ) : ℤ := if hj : j ≤ K then (hex j hj).choose else 0
  let Q : ℤ[X] := ∑ j ∈ Finset.range (K + 1), C (z j) * X ^ j
  have hQ : Q.natDegree ≤ K :=
    natDegree_sum_le_of_forall_le _ _ fun j hj =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hcoeff (j : ℕ) (hj : j ≤ K) : Q.coeff j = z j := by
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro h
      exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).elim
  obtain ⟨R, hR⟩ := exists_integer_approx_clear_inverse_affine p Q K hp hQ a b hb hS hB
    ((by norm_num : (0 : ℝ) ≤ 1).trans hH) ha hbB (fun j hj => by
      rw [hcoeff j hj]
      simpa only [z, dif_pos hj] using (hex j hj).choose_spec)
  exact fun j _ hj => ⟨R.coeff j, hR j hj⟩

/-- Undo sampling on an affine progression before applying the pair dilation
estimate. The uniform factor `b^K` can be put into both one-variable
polynomials before the product annihilator is frozen. -/
theorem pair_dilation_approx_of_affine
    (p₀ p₁ : ℝ[X]) (K : ℕ) (h₀ : p₀.natDegree ≤ K) (h₁ : p₁.natDegree ≤ K)
    (d e : ℝ) (a b : ℤ) (hb : b ≠ 0) {S B H : ℝ}
    (hS : 0 < S) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (ha : |(a : ℝ)| ≤ B * S) (hbB : |(b : ℝ)| ≤ B)
    (herror : ∀ j, 0 < j → j ≤ K → ∃ z : ℤ,
      |(p₀.comp (C d * (C (a : ℝ) + C (b : ℝ) * X)) +
        p₁.comp (C e * (C (a : ℝ) + C (b : ℝ) * X))).coeff j - (z : ℝ)| ≤ H / S ^ j) :
    ∀ j, 0 < j → j ≤ K → ∃ z : ℤ,
      |(C ((b : ℝ) ^ K) * p₀).coeff j * d ^ j +
        (C ((b : ℝ) ^ K) * p₁).coeff j * e ^ j - z| ≤
      (K + 1 : ℕ) * (2 : ℝ) ^ K * B ^ K * H / S ^ j := by
  let p := p₀.comp (C d * X) + p₁.comp (C e * X)
  have hdegree (f : ℝ[X]) (hf : f.natDegree ≤ K) (c : ℝ) :
      (f.comp (C c * X)).natDegree ≤ K := by
    have hc : (C c * X).natDegree ≤ 1 := by
      simpa only [pow_one] using natDegree_C_mul_X_pow_le c 1
    exact natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul hf hc)
  have hp : p.natDegree ≤ K :=
    (natDegree_add_le _ _).trans (max_le (hdegree p₀ h₀ d) (hdegree p₁ h₁ e))
  have herror' (j : ℕ) (hj : 0 < j) (hjK : j ≤ K) :
      ∃ z : ℤ, |(p.comp (C (a : ℝ) + C (b : ℝ) * X)).coeff j - (z : ℝ)| ≤ H / S ^ j := by
    simpa only [p, add_comp, comp_assoc, mul_comp, C_comp, X_comp] using herror j hj hjK
  intro j hj hjK
  obtain ⟨z, hz⟩ := exists_integer_approx_clear_inverse_affine_positive p K hp a b hb
    hS hB hH ha hbB herror' j hj hjK
  refine ⟨z, ?_⟩
  rw [coeff_C_mul, coeff_C_mul, mul_assoc ((b : ℝ) ^ K), mul_assoc ((b : ℝ) ^ K), ← mul_add]
  simpa only [p, coeff_pair_dilation] using hz

/-- Freeze the choice of a bounded label on a dense subset of dyadic pairs.
In the Type II argument a label records the same product annihilator throughout
the selected fiber. -/
private theorem exists_dense_label_fiber {α κ : Type*} [Fintype κ] [Nonempty κ]
    (G : Finset α) (label : α → κ) (M : ℝ)
    (hG : (Fintype.card κ : ℝ) * M ≤ (G.card : ℝ)) :
    ∃ c : κ, M ≤ ((G.filter fun z => label z = c).card : ℝ) := by
  have hcard : (Finset.univ : Finset κ).card • M ≤ (G.card : ℝ) := by
    simpa only [Finset.card_univ, nsmul_eq_mul] using hG
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (fun z (_ : z ∈ G) => Finset.mem_univ (label z)) Finset.univ_nonempty hcard
  exact ⟨c, hc⟩

/-- Combine coefficient denominators using a single product bound for the errors. -/
theorem common_denominator_of_bounded_coefficient_estimates {α : Type*} [Fintype α]
    (θ E : α → ℝ) (D : α → ℕ)
    (h : ∀ i, ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ q ≤ D i ∧ |(q : ℝ) * θ i - a| ≤ E i) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (∏ i, D i) ∧ ∀ i, ∃ a : ℤ,
      |(q : ℝ) * θ i - a| ≤ ((↑(∏ j, D j) : ℝ)) * E i := by
  classical
  obtain ⟨q, hq, hqD, hrec⟩ := common_denominator_of_coefficient_estimates θ E D h
  refine ⟨q, hq, hqD, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hrec i
  obtain ⟨b, z, hb, hbD, hE⟩ := h i
  refine ⟨a, ha.trans (mul_le_mul_of_nonneg_right ?_ ((abs_nonneg _).trans hE))⟩
  have hprod : (∏ j ∈ Finset.univ.erase i, D j) ≤ ∏ j, D j := by
    conv_rhs => rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)]
    exact Nat.le_mul_of_pos_left _ (hb.trans_le hbD)
  exact_mod_cast hprod

/-- Freeze one product annihilator and recover all of its two projected
coefficient families at the original scale. The final denominator works for
both sides, every annihilator row, and all degrees from one to `K`. -/
theorem recover_frozen_pair_dilation
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι]
    (p : κ → Bool → ι → ℝ[X]) (K L R : ℕ) {ρ H X₀ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X₀)
    (hRρ : 16 ≤ ρ * R) (hfreq : 16 * (R : ℝ) * H ≤ X₀ / L)
    (hden : ∀ j : Fin K,
      ((R * WeylInverse.leadingInverseBudget (j.val + 1) R : ℕ) : ℝ) * H ≤ X₀ / L)
    (hsize : ∀ j : Fin K, let B := WeylInverse.leadingInverseBudget (j.val + 1) R *
        2 ^ (j.val + 1) + 1
      8 * (2 * (B : ℝ) + 3) * ((↑(j.val + 1) : ℝ) + 1) ≤ ρ * L)
    (G : Finset (ℕ × ℕ)) (label : ℕ × ℕ → κ)
    (hG : G ⊆ dyadicDilationInterval L ×ˢ dyadicDilationInterval L)
    (hdense : let T := dyadicDilationInterval L
      (Fintype.card κ : ℝ) * (ρ * T.card * T.card) ≤ (G.card : ℝ))
    (hnear : ∀ z ∈ G, ∀ i j, 0 < j → j ≤ K → ∃ a : ℤ,
      |(p (label z) false i).coeff j * (z.1 : ℝ) ^ j +
        (p (label z) true i).coeff j * (z.2 : ℝ) ^ j - a| ≤ H / (X₀ / L) ^ j) :
    let D (j : Fin K) := WeylInverse.leadingInverseBudget (j.val + 1) R
    let Q (j : Fin K) := (R * D j) ^ 2
    let B (j : Fin K) := D j * 2 ^ (j.val + 1) + 1
    let C (j : Fin K) := 8 * (2 * (B j : ℝ) + 3) * ((↑(j.val + 1) : ℝ) + 1) / ρ
    let E (j : Fin K) := (Q j : ℝ) * interpolationCoefficientConstant (j.val + 1) *
      ((↑(j.val + 1) : ℝ) + 1) * C j ^ (j.val + 1) * H / X₀ ^ (j.val + 1)
    ∃ c : κ, ∃ q : ℕ, 0 < q ∧ q ≤ (∏ j : (ι × Fin K) × Bool, Q j.1.2) ∧
      ∀ i j v, ∃ a : ℤ, |(q : ℝ) * (p c v i).coeff (j.val + 1) - a| ≤
        ((↑(∏ x : (ι × Fin K) × Bool, Q x.1.2) : ℝ)) * E j := by
  intro D Q B C E
  let T := dyadicDilationInterval L
  obtain ⟨c, hc⟩ := exists_dense_label_fiber G label (ρ * T.card * T.card) hdense
  let θ (j : (ι × Fin K) × Bool) := (p c j.2 j.1.1).coeff (j.1.2.val + 1)
  have hrec (i : ι) (j : Fin K) :
      ∃ q : ℕ, 0 < q ∧ q ≤ Q j ∧ ∃ a b : ℤ,
        |(q : ℝ) * (p c false i).coeff (j.val + 1) - a| ≤ E j ∧
        |(q : ℝ) * (p c true i).coeff (j.val + 1) - b| ≤ E j := by
    let k := j.val + 1
    have hk : 0 < k := Nat.succ_pos _
    have hkK : k ≤ K := j.isLt
    have hcard : ρ * (T.card : ℝ) * (T.card : ℝ) ≤
        (((T ×ˢ T).filter (fun z : ℕ × ℕ => ∃ a : ℤ,
          |(p c false i).coeff k * (z.1 : ℝ) ^ k +
            (p c true i).coeff k * (z.2 : ℝ) ^ k - a| ≤ H / (X₀ / L) ^ k)).card : ℝ) := by
      apply hc.trans
      have hsub : (G.filter fun z => label z = c) ⊆
          (T ×ˢ T).filter (fun z : ℕ × ℕ => ∃ a : ℤ,
            |(p c false i).coeff k * (z.1 : ℝ) ^ k +
              (p c true i).coeff k * (z.2 : ℝ) ^ k - a| ≤ H / (X₀ / L) ^ k) := by
        intro z hz
        obtain ⟨hzG, hzlabel⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hG hzG,
          by simpa only [hzlabel] using hnear z hzG i k hk hkK⟩
      exact_mod_cast Finset.card_le_card hsub
    have h := recover_pair_dilation_dyadic L R hL (p c false i) (p c true i) hk hρ hH hLX
      hRρ hfreq (hden j) (hsize j) hcard
    simpa only [D, Q, B, C, E, Nat.cast_pow] using h
  have hθ (j : (ι × Fin K) × Bool) :
      ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ q ≤ Q j.1.2 ∧ |(q : ℝ) * θ j - a| ≤ E j.1.2 := by
    obtain ⟨⟨i, j⟩, v⟩ := j
    obtain ⟨q, hq, hqQ, a, b, ha, hb⟩ := hrec i j
    cases v
    · exact ⟨q, a, hq, hqQ, ha⟩
    · exact ⟨q, b, hq, hqQ, hb⟩
  obtain ⟨q, hq, hqQ, hqθ⟩ := common_denominator_of_bounded_coefficient_estimates θ
    (fun j => E j.1.2) (fun j => Q j.1.2) hθ
  exact ⟨c, q, hq, hqQ, fun i j v => hqθ ((i, j), v)⟩

/-- Recover a family of paired rows whose indices depend on degree. The
shared denominator includes the supplied integer multiplier of each row. -/
theorem recover_typeII_coefficient_rows {s : ℕ} {ι : Fin s → Type*} [∀ j, Fintype (ι j)]
    (θ : ∀ j, ι j → Bool → ℝ) (m : ∀ j, ι j → ℕ) (hm : ∀ j i, 0 < m j i)
    (L R : ℕ) {ρ H X₀ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X₀)
    (hRρ : 16 ≤ ρ * R) (hfreq : 16 * (R : ℝ) * H ≤ X₀ / L)
    (hden : ∀ j : Fin s,
      ((R * WeylInverse.leadingInverseBudget (j.val + 1) R : ℕ) : ℝ) * H ≤ X₀ / L)
    (hsize : ∀ j : Fin s, let B := WeylInverse.leadingInverseBudget (j.val + 1) R * 2 ^ (j.val + 1) + 1
      8 * (2 * (B : ℝ) + 3) * ((↑(j.val + 1) : ℝ) + 1) ≤ ρ * L)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ dyadicDilationInterval L ×ˢ dyadicDilationInterval L)
    (hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ^ 2 ≤ S.card)
    (hnear : ∀ d ∈ S, ∀ j i, ∃ a : ℤ,
      |((m j i : ℝ) * θ j i true) * (d.1 : ℝ) ^ (j.val + 1) +
        ((m j i : ℝ) * θ j i false) * (d.2 : ℝ) ^ (j.val + 1) - a| ≤ H / (X₀ / L) ^ (j.val + 1)) :
    let D (j : Fin s) := WeylInverse.leadingInverseBudget (j.val + 1) R
    let Q (j : Fin s) := (R * D j) ^ 2
    let B (j : Fin s) := D j * 2 ^ (j.val + 1) + 1
    let C (j : Fin s) := 8 * (2 * (B j : ℝ) + 3) * ((↑(j.val + 1) : ℝ) + 1) / ρ
    let E (j : Fin s) := (Q j : ℝ) * interpolationCoefficientConstant (j.val + 1) *
      ((↑(j.val + 1) : ℝ) + 1) * C j ^ (j.val + 1) * H
    let M (u : (Σ j : Fin s, ι j) × Bool) := Q u.1.1 * m u.1.1 u.1.2
    ∃ q : ℕ, 0 < q ∧ q ≤ (∏ u, M u) ∧
      ∀ j i v, ∃ a : ℤ, |(q : ℝ) * θ j i v - a| ≤ ((↑(∏ u, M u) : ℝ) * E j) / X₀ ^ (j.val + 1) := by
  classical
  intro D Q B C E M
  have hindividual (u : (Σ j : Fin s, ι j) × Bool) : ∃ q : ℕ, ∃ a : ℤ,
      0 < q ∧ q ≤ M u ∧ |(q : ℝ) * θ u.1.1 u.1.2 u.2 - a| ≤ E u.1.1 / X₀ ^ (u.1.1.val + 1) := by
    obtain ⟨⟨j, i⟩, v⟩ := u
    let k := j.val + 1
    let f (v : Bool) : ℝ[X] := Polynomial.monomial k ((m j i : ℝ) * θ j i v)
    have hcoeff (v : Bool) : (f v).coeff k = (m j i : ℝ) * θ j i v :=
      Polynomial.coeff_monomial_same _ _
    have hgood : let T := dyadicDilationInterval L
        ρ * (T.card : ℝ) * (T.card : ℝ) ≤
          (((T ×ˢ T).filter (fun d : ℕ × ℕ => ∃ a : ℤ,
            |(f true).coeff k * (d.1 : ℝ) ^ k + (f false).coeff k * (d.2 : ℝ) ^ k - a| ≤
              H / (X₀ / L) ^ k)).card : ℝ) := by
      dsimp only
      rw [mul_assoc, ← pow_two]
      apply hdense.trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro d hd
      exact Finset.mem_filter.mpr ⟨hS hd, by simpa only [hcoeff] using hnear d hd j i⟩
    obtain ⟨q, hq, hqQ, a, b, ha, hb⟩ := recover_pair_dilation_dyadic L R hL (f true) (f false)
      (Nat.succ_pos _) hρ hH hLX hRρ hfreq (hden j) (hsize j) hgood
    have hrec (v : Bool) : ∃ a : ℤ, |(q : ℝ) * (f v).coeff k - a| ≤ E j / X₀ ^ k := by
      cases v
      · exact ⟨b, by simpa only [E, Q, B, C, D, Nat.cast_pow] using hb⟩
      · exact ⟨a, by simpa only [E, Q, B, C, D, Nat.cast_pow] using ha⟩
    obtain ⟨a, ha⟩ := hrec v
    refine ⟨q * m j i, a, Nat.mul_pos hq (hm j i), Nat.mul_le_mul_right _ hqQ, ?_⟩
    rw [Nat.cast_mul, mul_assoc, ← hcoeff]
    exact ha
  obtain ⟨q, hq, hqM, happ⟩ := common_denominator_of_bounded_coefficient_estimates
    (fun u : (Σ j : Fin s, ι j) × Bool => θ u.1.1 u.1.2 u.2)
    (fun u => E u.1.1 / X₀ ^ (u.1.1.val + 1)) M hindividual
  refine ⟨q, hq, hqM, fun j i v => ?_⟩
  simpa only [mul_div_assoc] using happ (⟨j, i⟩, v)

/-- Freeze and recover a family of Type I constraints. The small-dilation
branch of the one-variable estimate allows this recovery even when the
dyadic interval is too short for interpolation. -/
theorem recover_frozen_single_dilation
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι]
    (p : κ → ι → ℝ[X]) (K L R : ℕ) {ρ H X₀ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X₀)
    (hRρ : 16 ≤ ρ * R) (hfreq : 16 * (R : ℝ) * H ≤ X₀ / L)
    (hden : ∀ j : Fin K,
      ((R * WeylInverse.leadingInverseBudget (j.val + 1) R : ℕ) : ℝ) * H ≤ X₀ / L)
    (G : Finset ℕ) (label : ℕ → κ)
    (hG : G ⊆ dyadicDilationInterval L)
    (hdense : (Fintype.card κ : ℝ) * (ρ * (dyadicDilationInterval L).card) ≤ (G.card : ℝ))
    (hnear : ∀ z ∈ G, ∀ i j, 0 < j → j ≤ K → ∃ a : ℤ,
      |(p (label z) i).coeff j * (z : ℝ) ^ j - a| ≤ H / (X₀ / L) ^ j) :
    let D (j : Fin K) := WeylInverse.leadingInverseBudget (j.val + 1) R
    let B (j : Fin K) := D j * 2 ^ (j.val + 1) + 1
    let S (j : Fin K) := 8 * (2 * (B j : ℝ) + 3) * ((↑(j.val + 1) : ℝ) + 1) / ρ
    let Q (j : Fin K) := max ((R * D j) ^ 2) (⌈S j⌉₊ ^ (j.val + 1))
    let C (j : Fin K) := ((R * D j : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant (j.val + 1) *
      ((↑(j.val + 1) : ℝ) + 1) * S j ^ (j.val + 1)
    let E (j : Fin K) := max (C j) (S j ^ (j.val + 1)) * H / X₀ ^ (j.val + 1)
    ∃ c : κ, ∃ q : ℕ, 0 < q ∧ q ≤ (∏ j : ι × Fin K, Q j.2) ∧
      ∀ i j, ∃ a : ℤ, |(q : ℝ) * (p c i).coeff (j.val + 1) - a| ≤
        ((↑(∏ x : ι × Fin K, Q x.2) : ℝ)) * E j := by
  intro D B S Q C E
  let T := dyadicDilationInterval L
  obtain ⟨c, hc⟩ := exists_dense_label_fiber G label (ρ * T.card) hdense
  let θ (j : ι × Fin K) := (p c j.1).coeff (j.2.val + 1)
  have hθ (w : ι × Fin K) :
      ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ q ≤ Q w.2 ∧ |(q : ℝ) * θ w - a| ≤ E w.2 := by
    obtain ⟨i, j⟩ := w
    let k := j.val + 1
    have hk : 0 < k := Nat.succ_pos _
    have hkK : k ≤ K := j.isLt
    have hcard : ρ * (T.card : ℝ) ≤
        ((T.filter (fun z : ℕ => ∃ a : ℤ,
          |(p c i).coeff k * (z : ℝ) ^ k - a| ≤ H / (X₀ / L) ^ k)).card : ℝ) := by
      apply hc.trans
      have hsub : (G.filter fun z => label z = c) ⊆
          T.filter (fun z : ℕ => ∃ a : ℤ, |(p c i).coeff k * (z : ℝ) ^ k - a| ≤ H / (X₀ / L) ^ k) := by
        intro z hz
        obtain ⟨hzG, hzlabel⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hG hzG,
          by simpa only [hzlabel] using hnear z hzG i k hk hkK⟩
      exact_mod_cast Finset.card_le_card hsub
    obtain ⟨q, hq, hqQ, a, ha⟩ :=
      recover_single_dilation_dyadic L R hL (p c i) hk hρ hH hLX hRρ hfreq (hden j) hcard
    exact ⟨q, a, hq, hqQ, ha⟩
  obtain ⟨q, hq, hqQ, hqθ⟩ := common_denominator_of_bounded_coefficient_estimates θ
    (fun j => E j.2) (fun j => Q j.2) hθ
  exact ⟨c, q, hq, hqQ, fun i j => hqθ (i, j)⟩

end PrimeUniformity
