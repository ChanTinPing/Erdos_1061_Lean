module

public import PrimeUniformity.DilationDescent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Classical BigOperators

/-- Fixed-degree Type II recovery only needs exponential side lengths.
The common denominator and errors at the full scale have logarithms
quadratic in the logarithmic input budget. -/
theorem exists_uniform_typeII_coefficient_recovery (s : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {J : Fin s → Type*} [∀ j, Fintype (J j)] (θ : ∀ j, J j → Bool → ℝ)
        (m : ∀ j, J j → ℕ) (_hm : ∀ j i, 0 < m j i) (L : ℕ) {t H X₀ X : ℝ},
      1 ≤ t → 0 ≤ H → H ≤ Real.exp t → (∀ j i, (m j i : ℝ) ≤ Real.exp t) →
      (Fintype.card ((Σ j : Fin s, J j) × Bool) : ℝ) ≤ t →
      Real.exp ((C : ℝ) * t) ≤ L → Real.exp ((C : ℝ) * t) ≤ X₀ / L →
      0 < X → X * Real.exp (-t) ≤ X₀ →
      ∀ (S : Finset (ℕ × ℕ)), S ⊆ dyadicDilationInterval L ×ˢ dyadicDilationInterval L →
      Real.exp (-t) * ((dyadicDilationInterval L).card : ℝ) ^ 2 ≤ S.card →
      (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * θ j i true) * (d.1 : ℝ) ^ (j.val + 1) +
          ((m j i : ℝ) * θ j i false) * (d.2 : ℝ) ^ (j.val + 1) - a| ≤
            H / (X₀ / L) ^ (j.val + 1)) →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((C : ℝ) * t ^ 2) ∧
        ∀ j i v, ∃ a : ℤ, |(q : ℝ) * θ j i v - a| ≤ Real.exp ((C : ℝ) * t ^ 2) / X ^ (j.val + 1) := by
  obtain ⟨c, _, hc⟩ := exists_uniform_leadingInverseBudget_exp_bound s
  let K : ℝ := 40 + 2 ^ s + (s : ℝ) + 1 +
    ∑ k ∈ Finset.range (s + 1), |interpolationCoefficientConstant k|
  obtain ⟨A, hA⟩ := exists_nat_gt (K + 18 * c + 18)
  let C := (12 + 7 * s) * A
  have hsum₀ : 0 ≤ ∑ k ∈ Finset.range (s + 1), |interpolationCoefficientConstant k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hs₀ : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have h2s₀ : (0 : ℝ) ≤ 2 ^ s := by positivity
  have hK : 40 ≤ K := by dsimp only [K]; linarith
  have hA₁ : 1 ≤ A := by
    have hc₀ : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
  have hCA : A ≤ C := by
    dsimp only [C]
    simpa only [one_mul] using Nat.mul_le_mul_right A (show 1 ≤ 12 + 7 * s by omega)
  have hC : 1 ≤ C := hA₁.trans hCA
  refine ⟨C, hC, ?_⟩
  intro J _ θ m hm L t H X₀ X ht hH hHt hmt hcard hL hside hX hX₀ S hS hdense hnear
  let U := Real.exp ((A : ℝ) * t)
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hAt : (A : ℝ) ≤ (A : ℝ) * t := le_mul_of_one_le_right (Nat.cast_nonneg _) ht
  have hAU : (A : ℝ) ≤ U := hAt.trans (by linarith [Real.add_one_le_exp ((A : ℝ) * t)])
  have hKU : K ≤ U := by linarith [Nat.cast_nonneg (α := ℝ) c]
  have hU₄₀ : 40 ≤ U := hK.trans hKU
  have hU₁ : 1 ≤ U := by linarith
  have hU₀ : 0 ≤ U := zero_le_one.trans hU₁
  have heU : Real.exp t ≤ U :=
    Real.exp_le_exp.mpr (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by exact_mod_cast hA₁ : (1 : ℝ) ≤ A) ht₀)
  obtain ⟨R, _, hRρ, hR⟩ := exists_dilation_frequency_cutoff (Real.exp_pos (-t))
  have hR' : (R : ℝ) ≤ Real.exp (18 * t) := by
    refine hR.trans ?_
    rw [Real.exp_neg, div_inv_eq_mul]
    have hex : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht₀
    have h17 : (17 : ℝ) ≤ Real.exp (17 * t) := by linarith [Real.add_one_le_exp (17 * t)]
    calc
      _ ≤ 17 * Real.exp t := by linarith
      _ ≤ Real.exp (17 * t) * Real.exp t := mul_le_mul_of_nonneg_right h17 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hRU : (R : ℝ) ≤ U := hR'.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) c]) ht₀))
  let D (j : Fin s) := WeylInverse.leadingInverseBudget (j.val + 1) R
  let Q (j : Fin s) := (R * D j) ^ 2
  let B (j : Fin s) := D j * 2 ^ (j.val + 1) + 1
  let N (j : Fin s) := 8 * (2 * (B j : ℝ) + 3) * ((j.val + 1 : ℕ) + 1 : ℝ)
  let E (j : Fin s) := (Q j : ℝ) * interpolationCoefficientConstant (j.val + 1) *
    ((↑(j.val + 1) : ℝ) + 1) * (N j / Real.exp (-t)) ^ (j.val + 1) * H
  let M (u : (Σ j : Fin s, J j) × Bool) := Q u.1.1 * m u.1.1 u.1.2
  have hk (j : Fin s) : j.val + 1 ≤ s := j.isLt
  have hDU (j : Fin s) : (D j : ℝ) ≤ U := by
    apply (hc _ (hk j) (by linarith : 1 ≤ 18 * t) R hR').trans
    apply Real.exp_le_exp.mpr
    have hA' : 18 * (c : ℝ) ≤ A := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hA' ht₀]
  have hpow (j : Fin s) : (2 : ℝ) ^ (j.val + 1) ≤ U := by
    refine (pow_le_pow_right₀ (by norm_num) (hk j)).trans ?_
    apply le_trans _ hKU
    dsimp only [K]
    linarith
  have hlin (j : Fin s) : ((↑(j.val + 1) : ℝ) + 1) ≤ U := by
    refine le_trans (add_le_add (by exact_mod_cast hk j : ((j.val + 1 : ℕ) : ℝ) ≤ s) le_rfl) ?_
    apply le_trans _ hKU
    dsimp only [K]
    linarith
  have hI (j : Fin s) : interpolationCoefficientConstant (j.val + 1) ≤ U := by
    refine (le_abs_self _).trans ((Finset.single_le_sum
      (fun k _ => abs_nonneg (interpolationCoefficientConstant k))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk j)))).trans ?_)
    apply le_trans _ hKU
    dsimp only [K]
    linarith
  have hI₀ (j : Fin s) : 0 ≤ interpolationCoefficientConstant (j.val + 1) := by
    unfold interpolationCoefficientConstant
    apply add_nonneg zero_le_one
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBU (j : Fin s) : (B j : ℝ) ≤ U ^ 3 := by
    push_cast [B]
    have hp : (D j : ℝ) * 2 ^ (j.val + 1) ≤ U * U :=
      mul_le_mul (hDU j) (hpow j) (by positivity) hU₀
    have h₁ : 1 ≤ U ^ 2 := one_le_pow₀ hU₁
    nlinarith only [hp, h₁, mul_le_mul_of_nonneg_right (show 2 ≤ U by linarith)
      (sq_nonneg U)]
  have hNU (j : Fin s) : N j ≤ U ^ 5 := by
    have hB : 2 * (B j : ℝ) + 3 ≤ 5 * U ^ 3 := by
      nlinarith only [hBU j, one_le_pow₀ hU₁ (n := 3)]
    calc
      _ ≤ 8 * (5 * U ^ 3) * U := by dsimp [N]; gcongr; exact hlin j
      _ = 40 * U ^ 4 := by ring
      _ ≤ U ^ 5 := by
        rw [show U ^ 5 = U ^ 4 * U from pow_succ _ _, mul_comm (40 : ℝ)]
        exact mul_le_mul_of_nonneg_left hU₄₀ (pow_nonneg hU₀ _)
  have hQU (j : Fin s) : (Q j : ℝ) ≤ U ^ 4 := by
    push_cast [Q]
    calc
      _ ≤ (U * U) ^ 2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul hRU (hDU j) (Nat.cast_nonneg _) hU₀) _
      _ = _ := by ring
  have hCU (j : Fin s) : N j / Real.exp (-t) ≤ U ^ 6 := by
    rw [Real.exp_neg, div_inv_eq_mul, pow_succ]
    exact mul_le_mul (hNU j) heU (Real.exp_pos _).le (pow_nonneg hU₀ _)
  have hHU : H ≤ U := hHt.trans heU
  have hE₀ (j : Fin s) : 0 ≤ E j := by
    have hIj := hI₀ j
    dsimp [E, N]
    positivity
  have hEU (j : Fin s) : E j ≤ U ^ (7 + 6 * s) := by
    have hpower : (N j / Real.exp (-t)) ^ (j.val + 1) ≤ U ^ (6 * s) := by
      rw [pow_mul]
      exact (pow_le_pow_left₀ (by dsimp [N]; positivity) (hCU j) _).trans
        (pow_le_pow_right₀ (one_le_pow₀ hU₁) (hk j))
    calc
      _ ≤ U ^ 4 * U * U * U ^ (6 * s) * U := by dsimp [E]; gcongr <;>
        first | exact hQU j | exact hI j | exact hlin j | exact hpower | exact hHU |
          exact hI₀ j
      _ = _ := by simp only [pow_add, show U ^ 7 = U ^ 4 * U * U * U by ring]; ring
  have hscale : U ^ 6 ≤ Real.exp ((C : ℝ) * t) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp only [C]
    push_cast
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ (6 + 7 * (s : ℝ)) * A by positivity) ht₀]
  have hLp : 0 < L := Nat.cast_pos.mp ((Real.exp_pos _).trans_le hL)
  have hside₁ : 1 ≤ X₀ / L := (one_le_pow₀ hU₁).trans (hscale.trans hside)
  have hLX : (L : ℝ) ≤ X₀ := (one_le_div (Nat.cast_pos.mpr hLp)).mp hside₁
  have hlow (k : ℕ) (hk : k ≤ 6) : U ^ k ≤ Real.exp ((C : ℝ) * t) :=
    (pow_le_pow_right₀ hU₁ hk).trans hscale
  have hfreq : 16 * (R : ℝ) * H ≤ X₀ / L := calc
    _ ≤ U * U * U := by gcongr; linarith
    _ = U ^ 3 := by ring
    _ ≤ _ := (hlow 3 (by decide)).trans hside
  have hden (j : Fin s) : ((R * D j : ℕ) : ℝ) * H ≤ X₀ / L := calc
    _ ≤ U * U * U := by
      push_cast
      exact mul_le_mul (mul_le_mul hRU (hDU j) (Nat.cast_nonneg _) hU₀) hHU hH
        (mul_nonneg hU₀ hU₀)
    _ = U ^ 3 := by ring
    _ ≤ _ := (hlow 3 (by decide)).trans hside
  have hsize (j : Fin s) : N j ≤ Real.exp (-t) * L := by
    have h := (hCU j).trans (hscale.trans hL)
    simpa only [mul_comm] using (div_le_iff₀ (Real.exp_pos (-t))).mp h
  obtain ⟨q, hq, hqM, ha⟩ := recover_typeII_coefficient_rows θ m hm L R hLp
    (Real.exp_pos (-t)) hH hLX hRρ hfreq hden hsize S hS hdense hnear
  have hprod : ((∏ u, M u : ℕ) : ℝ) ≤ Real.exp (5 * A * t ^ 2) := calc
    _ ≤ ∏ _ : (Σ j : Fin s, J j) × Bool, U ^ 5 := by
      rw [Nat.cast_prod]
      first | apply Finset.prod_le_prod₀ | apply Finset.prod_le_prod
      · exact fun _ _ => Nat.cast_nonneg _
      intro u _
      push_cast [M]
      rw [pow_succ]
      exact mul_le_mul (hQU u.1.1) ((hmt u.1.1 u.1.2).trans heU) (Nat.cast_nonneg _)
        (pow_nonneg hU₀ _)
    _ = Real.exp (((Fintype.card ((Σ j : Fin s, J j) × Bool) : ℕ) : ℝ) * (5 * (A * t))) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hnonneg : 0 ≤ 5 * ((A : ℝ) * t) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hcard hnonneg])
  have hfinal : 5 * (A : ℝ) * t ^ 2 + (A * t) * (7 + 6 * s) + s * t ≤ (C : ℝ) * t ^ 2 := by
    have hst : 0 ≤ (s : ℝ) * t := by positivity
    have h₁ : (s : ℝ) * t ≤ (s : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_left (le_self_pow₀ ht (by decide)) (Nat.cast_nonneg _)
    have h₂ : (s : ℝ) * t ^ 2 ≤ s * A * t ^ 2 := by
      have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA₁
      nlinarith only [mul_le_mul_of_nonneg_right hA' (mul_nonneg hs₀ (sq_nonneg t))]
    have h₃ := mul_le_mul_of_nonneg_left (le_self_pow₀ ht (by decide : (2 : ℕ) ≠ 0))
      (show 0 ≤ (A : ℝ) * (7 + 6 * (s : ℝ)) by positivity)
    dsimp [C]
    push_cast
    nlinarith only [h₁, h₂, h₃]
  have hfinal' : 5 * (A : ℝ) * t ^ 2 ≤ (C : ℝ) * t ^ 2 :=
    (le_add_of_nonneg_right (by positivity)).trans ((le_add_of_nonneg_right (by positivity)).trans hfinal)
  refine ⟨q, hq, (Nat.cast_le.mpr hqM).trans (hprod.trans (Real.exp_le_exp.mpr hfinal')), ?_⟩
  intro j i v
  obtain ⟨a, ha⟩ := ha j i v
  refine ⟨a, ha.trans ?_⟩
  change ((∏ u, M u : ℕ) : ℝ) * E j / X₀ ^ (j.val + 1) ≤ _
  have hX₀p : 0 < X₀ := (mul_pos hX (Real.exp_pos _)).trans_le hX₀
  calc
    _ ≤ (Real.exp (5 * A * t ^ 2) * U ^ (7 + 6 * s)) /
        (X * Real.exp (-t)) ^ (j.val + 1) := by
      gcongr <;> first | exact hprod | exact hEU j | exact hX₀ | exact hE₀ j
    _ = (Real.exp (5 * A * t ^ 2) * U ^ (7 + 6 * s) *
        Real.exp (t * (j.val + 1))) / X ^ (j.val + 1) := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      rw [show (j.val + 1 : ℝ) * -t = -(t * (j.val + 1)) by ring, Real.exp_neg]
      rw [div_mul_eq_div_div, div_inv_eq_mul]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hX.le _)
      dsimp only [U]
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htk := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hk j) : ((j.val + 1 : ℕ) : ℝ) ≤ s) ht₀
      push_cast at htk ⊢
      nlinarith only [hfinal, htk]

end PrimeUniformity
