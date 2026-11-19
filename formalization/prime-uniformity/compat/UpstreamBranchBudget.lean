import UpstreamPrimeRankIteration
import UpstreamVerticalDescent

namespace PrimeUniformity

open OAI.Erdos3

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

theorem natPolynomial_eval₂_real_nonneg (P : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp i)

/-- A single polynomial bound can pay the coefficient-recovery thresholds
for both branches and the cost of the resulting test. -/
theorem exists_prepared_branch_polynomial_budget (P : Polynomial ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {X : ℕ} {p : ℝ}, 2 ≤ p →
      p ^ C ≤ Real.log (X : ℝ) ^ (1 / 2 : ℝ) →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ p ^ C ∧
      P.eval₂ (Nat.castRingHom ℝ) p ≤ Real.log (X : ℝ) ∧
      P.eval₂ (Nat.castRingHom ℝ) p + Real.log 4 ≤ Real.log (X : ℝ) / 4 := by
  obtain ⟨K, _, hK⟩ := exists_natPolynomial_eval_le_power P
  let C := K + 3
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro X p hp hsize
  let u := p ^ C
  have hp₁ : 1 ≤ p := by linarith
  have hKle : K ≤ C := by dsimp only [C]; omega
  have hThree : 3 ≤ C := by dsimp only [C]; omega
  have hEight : 8 ≤ u := by
    refine le_trans ?_ (pow_le_pow_right₀ hp₁ hThree)
    simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp 3
  have hu₀ : 0 ≤ u := by linarith
  have hPu : P.eval₂ (Nat.castRingHom ℝ) p ≤ u :=
    (hK p hp).trans (pow_le_pow_right₀ hp₁ hKle)
  rw [← Real.sqrt_eq_rpow] at hsize
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    (Real.sqrt_pos.mp ((by linarith only [hEight] : 0 < u).trans_le hsize)).le
  have hsq : u ^ 2 ≤ Real.log (X : ℝ) :=
    (pow_le_pow_left₀ hu₀ hsize 2).trans_eq (Real.sq_sqrt hlog)
  have hquad : 2 * u ≤ u ^ 2 / 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hEight hu₀]
  have hlog₄ : Real.log 4 ≤ 3 := by
    simpa only [show (4 : ℝ) - 1 = 3 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  refine ⟨hPu, hPu.trans ((by nlinarith only [hquad, hu₀] : u ≤ u ^ 2).trans hsq), ?_⟩
  calc
    _ ≤ u + Real.log 4 := add_le_add hPu le_rfl
    _ ≤ 2 * u := by linarith only [hEight, hlog₄]
    _ ≤ u ^ 2 / 4 := hquad
    _ ≤ _ := div_le_div_of_nonneg_right hsq (by norm_num)

/-- Raising the complexity budget preserves a ranked test's evaluations and
its correlation above the corresponding exponential threshold. -/
theorem nativeRankedPrimeTest_promote_correlation {s r X : ℕ} {p q : ℝ}
    (hpq : p ≤ q) (W : NativeRankedPrimeTest s r X p) (w : ℤ → ℝ)
    (hcorr : Real.exp (-p) < intervalCorrelation X w W.test.eval) :
    ∃ G : NativeRankedPrimeTest s r X q, G.test.eval = W.test.eval ∧
      Real.exp (-q) < intervalCorrelation X w G.test.eval := by
  let G : NativeRankedPrimeTest s r X q :=
    ⟨{ W.test with complexity := W.test.complexity.mono hpq }, W.rank, W.complexity.mono W.rank hpq⟩
  exact ⟨G, rfl, (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt hcorr⟩

end PrimeUniformity
