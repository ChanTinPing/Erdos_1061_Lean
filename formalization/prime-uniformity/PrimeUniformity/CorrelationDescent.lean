module

public import PrimeUniformity.PrimeProgressionTests
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- A uniform approximation by a finite sum of tests preserves a
correlation up to the approximation error and the number of tests. -/
theorem exists_large_intervalCorrelation_component {ι : Type*} {X : ℕ} (hX : 0 < X)
    (J : Finset ι) (w : ℤ → ℝ) (F : ℤ → ℂ) (G : ι → ℤ → ℂ) {B ρ : ℝ}
    (hB : 0 ≤ B)
    (hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ B)
    (happrox : ∀ n ∈ interval 1 (X : ℤ), ‖F n - ∑ j ∈ J, G j n‖ ≤ ρ)
    (hlarge : B * ρ < intervalCorrelation X w F) :
    ∃ j ∈ J, intervalCorrelation X w F ≤
      B * ρ + (J.card : ℝ) * intervalCorrelation X w (G j) := by
  let I := interval 1 (X : ℤ)
  let L (H : ℤ → ℂ) := ∑ n ∈ I, (w n : ℂ) * star (H n)
  have hcard : (I.card : ℝ) = (X : ℝ) := by
    simpa using card_interval 1 (X : ℤ) (by positivity)
  have hcardC : (I.card : ℂ) = (X : ℂ) := by exact_mod_cast hcard
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hcorr (H : ℤ → ℂ) : intervalCorrelation X w H = ‖L H‖ / (X : ℝ) := by
    change ‖𝔼 n ∈ I, (w n : ℂ) * star (H n)‖ = _
    rw [Finset.expect_eq_sum_div_card, hcardC, norm_div, Complex.norm_natCast]
  have hsum : L (fun n => ∑ j ∈ J, G j n) = ∑ j ∈ J, L (G j) := by
    simp only [L, star_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have herror : ‖L F - ∑ j ∈ J, L (G j)‖ ≤ (X : ℝ) * (B * ρ) := by
    rw [← hsum]
    simp only [L, ← Finset.sum_sub_distrib, ← mul_sub, ← star_sub]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _n ∈ I, B * ρ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
        exact mul_le_mul (hw n hn) (happrox n hn) (norm_nonneg _) hB
      _ = _ := by simp [nsmul_eq_mul, hcard]
  have htri : ‖L F‖ ≤ (X : ℝ) * (B * ρ) + ‖∑ j ∈ J, L (G j)‖ := by
    calc
      _ = ‖(L F - ∑ j ∈ J, L (G j)) + ∑ j ∈ J, L (G j)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add herror le_rfl)
  have hJ : J.Nonempty := by
    by_contra hJ
    rw [Finset.not_nonempty_iff_eq_empty.mp hJ, Finset.sum_empty, norm_zero, add_zero] at htri
    exact (not_le_of_gt hlarge) (by
      rw [hcorr]
      exact (div_le_iff₀ hXR).mpr (by simpa only [mul_comm (X : ℝ)] using htri))
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J (fun j => ‖L (G j)‖) hJ
  refine ⟨j, hj, ?_⟩
  rw [hcorr, hcorr]
  apply (div_le_iff₀ hXR).mpr
  calc
    _ ≤ (X : ℝ) * (B * ρ) + ‖∑ i ∈ J, L (G i)‖ := htri
    _ ≤ (X : ℝ) * (B * ρ) + (J.card : ℝ) * ‖L (G j)‖ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ i ∈ J, ‖L (G i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ J, ‖L (G j)‖ := Finset.sum_le_sum hmax
        _ = _ := by simp [nsmul_eq_mul]
    _ = _ := by field_simp

/-- Tests of step zero are finite sums of constants on arithmetic
progressions, with an exponential bound in their logarithmic budget. -/
def ProgressionCombination (X : ℕ) (p : ℝ) : Set (ℤ → ℂ) :=
  {F | ∃ (m : ℕ) (U V q : Fin m → ℕ) (a : ∀ i, ZMod (q i)) (z : Fin m → ℂ),
    (∀ i, U i ≤ V i ∧ V i ≤ X ∧ 0 < q i) ∧ (∑ i, ‖z i‖) ≤ Real.exp p ∧
    F = fun n => ∑ i, if n ∈ residueSlice ((U i : ℤ) + 1) ((V i - U i : ℕ) : ℤ) (a i)
      then z i else 0}

/-- Iterate a one-step descent of a large correlation, accounting for the
power loss at every step. -/
theorem correlation_le_of_step_descent (tests : ℕ → ℝ → Set (ℤ → ℂ))
    (corr : (ℤ → ℂ) → ℝ) (s : ℕ) {C : ℕ} (hC : 1 ≤ C) {P₀ B : ℝ} (hP₀ : 1 ≤ P₀)
    (hbase : ∀ p : ℝ, P₀ ≤ p → p ≤ B → ∀ F ∈ tests 0 p, corr F ≤ Real.exp (-p))
    (hstep : ∀ k < s, ∀ p, P₀ ≤ p → p ^ C ≤ B → ∀ F ∈ tests (k + 1) p,
      Real.exp (-p) < corr F → ∃ G ∈ tests k (p ^ C), Real.exp (-(p ^ C)) < corr G) :
    ∀ k ≤ s, ∀ p, P₀ ≤ p → p ^ (C ^ k) ≤ B → ∀ F ∈ tests k p, corr F ≤ Real.exp (-p) := by
  intro k
  induction k with
  | zero =>
    intro _ p hp hB F hF
    exact hbase p hp (by simpa using hB) F hF
  | succ k ih =>
    intro hks p hp hB F hF
    have hp₁ : 1 ≤ p := hP₀.trans hp
    have hpow : p ≤ p ^ C := by
      simpa only [pow_one] using (pow_le_pow_right₀ hp₁ hC)
    have hk : 1 ≤ C ^ k := Nat.one_le_pow _ _ (by omega)
    have hsmall : p ^ C ≤ B := by
      refine (pow_le_pow_right₀ hp₁ (show C ≤ C ^ (k + 1) from ?_)).trans hB
      rw [pow_succ]
      exact Nat.le_mul_of_pos_left C hk
    by_contra! hlarge
    obtain ⟨G, hG, hlarge⟩ := hstep k hks p hp hsmall F hF hlarge
    have hB' : (p ^ C) ^ (C ^ k) ≤ B := by
      rw [← pow_mul, mul_comm C, ← pow_succ]
      exact hB
    exact (not_lt_of_ge (ih (Nat.le_of_lt hks) _ (hp.trans hpow) hB' G hG)) hlarge

/-- The required output of the Type I/II descent for a bounded number of
steps. The budget may grow by a fixed power at each step, and the lower
bound on the budget allows the logarithmic loss in the finite decomposition. -/
def PrimeCramerStepDescent (s : ℕ) (tests : ℕ → ℕ → ℝ → Set (ℤ → ℂ)) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ k < s, ∀ p : ℝ, max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ C ≤ Real.log (X : ℝ) ^ b →
      ∀ F ∈ tests (k + 1) X p,
        Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) F →
      ∃ G ∈ tests k X (p ^ C),
        Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G

/-- Arithmetic-progression estimates close the descent. This converts a
bounded number of step drops into the orthogonality needed by the interval
inverse theorem. -/
theorem eventually_prime_cramer_orthogonal_of_descent {s : ℕ}
    (tests : ℕ → ℕ → ℝ → Set (ℤ → ℂ)) (hprime : UniformPrimePrefixEstimate)
    (hmono : ∀ X, Monotone (tests s X))
    (hzero : ∀ X p, tests 0 X p ⊆ ProgressionCombination X p)
    (hdescent : PrimeCramerStepDescent s tests) :
    ∃ b M : ℝ, 0 < b ∧ 0 < M ∧ ∀ᶠ X : ℕ in atTop,
      ∀ p : ℝ, p ≤ Real.log (X : ℝ) ^ b → ∀ F ∈ tests s X p,
        intervalCorrelation X (strictVonMangoldtCramerDifference X) F ≤
          M * Real.exp (-(Real.log (X : ℝ) ^ b)) := by
  obtain ⟨C, hC, e, he, hstep⟩ := hdescent
  obtain ⟨c, D, hc, hD, hprog⟩ := uniform_prime_cramer_progression_tests hprime
  let b₀ := min e (1 / 40 : ℝ)
  let b := b₀ / (C ^ s : ℕ)
  have hb₀ : 0 < b₀ := lt_min he (by norm_num)
  have hCpos : (0 : ℝ) < (C ^ s : ℕ) := by exact_mod_cast (pow_pos hC s)
  have hb : 0 < b := div_pos hb₀ hCpos
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbAtTop := (tendsto_rpow_atTop hb).comp hlog
  have h40AtTop := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 40 by norm_num)).comp hlog
  have hslow := hlog.eventually ((isLittleO_log_rpow_atTop hb).bound one_pos)
  refine ⟨b, 1, hb, one_pos, ?_⟩
  filter_upwards [hstep, hprog, hlog.eventually_ge_atTop 1, hbAtTop.eventually_ge_atTop 2, hslow,
    h40AtTop.eventually_ge_atTop ((2 + max 0 (Real.log D)) / c)]
    with X hstep hprog hlog hp₂ hslow h40
  intro p hp F hF
  let L := Real.log (X : ℝ)
  let P := L ^ b
  let P₀ := max 2 (Real.log L)
  let B := L ^ b₀
  let T := L ^ (1 / 40 : ℝ)
  have hLpos : 0 < L := zero_lt_one.trans_le hlog
  have hP₀ : 1 ≤ P₀ := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hPmin : P₀ ≤ P := by
    refine max_le hp₂ ((le_abs_self _).trans ?_)
    change ‖Real.log L‖ ≤ 1 * ‖P‖ at hslow
    have hP : 0 ≤ P := Real.rpow_nonneg hLpos.le _
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hP] using hslow
  have hTe : B ≤ L ^ e := Real.rpow_le_rpow_of_exponent_le hlog (min_le_left _ _)
  have hT : B ≤ T := Real.rpow_le_rpow_of_exponent_le hlog (min_le_right _ _)
  have hbudget : P ^ (C ^ s) ≤ B := by
    dsimp only [P, B]
    rw [← Real.rpow_mul_natCast hLpos.le]
    rw [show b * (C ^ s : ℕ) = b₀ from div_mul_cancel₀ b₀ hCpos.ne']
  have hbase : ∀ q : ℝ, P₀ ≤ q → q ≤ B → ∀ G ∈ tests 0 X q,
      intervalCorrelation X (strictVonMangoldtCramerDifference X) G ≤ Real.exp (-q) := by
    intro q hq hqB G hG
    obtain ⟨m, U, V, r, a, z, hparams, hz, rfl⟩ := hzero X q hG
    have hzprog := hprog Finset.univ U V r a z (fun i _ => hparams i)
    have hscan : Real.log D + 2 * q ≤ c * L ^ (1 / 20 : ℝ) := by
      have hTsq : T ^ (2 : ℕ) = L ^ (1 / 20 : ℝ) := by
        dsimp only [T]
        rw [← Real.rpow_mul_natCast hLpos.le]
        norm_num
      have hT₁ : 1 ≤ T := hP₀.trans (hq.trans (hqB.trans hT))
      have hmax : Real.log D ≤ max 0 (Real.log D) * T :=
        (le_max_right _ _).trans (le_mul_of_one_le_right (le_max_left _ _) hT₁)
      have hcT : 2 + max 0 (Real.log D) ≤ c * T := by
        have ih := (div_le_iff₀ hc).mp h40
        calc
          _ ≤ T * c := ih
          _ = _ := mul_comm _ _
      rw [← hTsq, pow_two, ← mul_assoc]
      have hqT := hqB.trans hT
      nlinarith [mul_le_mul_of_nonneg_right hcT (zero_le_one.trans hT₁)]
    refine hzprog.trans ((mul_le_mul_of_nonneg_left hz (by positivity)).trans ?_)
    rw [← Real.exp_log hD, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hlast := correlation_le_of_step_descent (fun k => tests k X)
    (intervalCorrelation X (strictVonMangoldtCramerDifference X)) s hC hP₀ hbase ?_ s le_rfl P hPmin hbudget
    F (hmono X hp hF)
  · simpa only [one_mul] using hlast
  · intro k hk q hq hqC G hG hlarge
    exact hstep k hk q hq (hqC.trans hTe) G hG hlarge

end PrimeUniformity
