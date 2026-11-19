module

public import PrimeUniformity.IntervalNorm
public import PrimeUniformity.StrictCutoffTransfer
public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter
open scoped BigOperators

/-- Absolute correlation with a complex test, averaged over the integer interval. -/
noncomputable def intervalCorrelation (X : ℕ) (w : ℤ → ℝ) (F : ℤ → ℂ) : ℝ :=
  ‖𝔼 n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ)), (w n : ℂ) * star (F n)‖

/-- The weight tested in the quantitative inverse theorem uses the strict cutoff. -/
noncomputable def strictVonMangoldtCramerDifference (X : ℕ) (n : ℤ) : ℝ :=
  vonMangoldtWeight n - cramerWeight (strictPrimeUniformityCutoff X) n

/-- A quantitative inverse theorem with a fixed polynomial loss in the log
of the inverse correlation, for a family of tests indexed by size and budget. -/
def IntervalCorrelationInverse (order : ℕ) (tests : ℕ → ℝ → Set (ℤ → ℂ)) : Prop :=
  ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : ℕ), 0 < X → ∀ p : ℝ, 2 ≤ p →
    ∀ w : ℤ → ℝ, (∀ n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ)), |w n| ≤ 1) →
    Real.exp (-p) ≤ intervalGowersNorm order X w →
    ∃ F ∈ tests X ((p + C) ^ C), Real.exp (-((p + C) ^ C)) ≤ intervalCorrelation X w F

private theorem intervalCorrelation_mul_const (X : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (w : ℤ → ℝ) (F : ℤ → ℂ) :
    intervalCorrelation X (fun n => a * w n) F = a * intervalCorrelation X w F := by
  simp only [intervalCorrelation, Complex.ofReal_mul, mul_assoc, ← Finset.mul_expect,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]

/-- The normalized inverse argument and vertical selection both use this
uniform pointwise bound for the strict Cramér comparison weight. -/
theorem eventually_abs_strictVonMangoldtCramerDifference :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ X : ℕ in atTop,
      ∀ n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ)),
        |strictVonMangoldtCramerDifference X n| ≤ B * Real.log (X : ℝ) ^ (8 : ℕ) := by
  obtain ⟨B, hB, hcramer⟩ := eventually_abs_cramerWeight_le_log_pow
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨1 + B, by linarith, ?_⟩
  filter_upwards [hcramer, hlog.eventually_ge_atTop 1] with X hcramer hlog
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  have hprime : |vonMangoldtWeight n| ≤ Real.log (X : ℝ) := by
    rw [vonMangoldtWeight, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast (show 0 < n.toNat by omega))
        (by exact_mod_cast (show n.toNat ≤ X by omega)))
  calc
    _ ≤ |vonMangoldtWeight n| + |cramerWeight (strictPrimeUniformityCutoff X) n| := abs_sub _ _
    _ ≤ Real.log (X : ℝ) + B * Real.log (X : ℝ) ^ (8 : ℕ) :=
      add_le_add hprime (hcramer _ (strictPrimeUniformityCutoff_le X) n)
    _ ≤ _ := by
      rw [add_mul, one_mul]
      have hpow := pow_le_pow_right₀ hlog (show (1 : ℕ) ≤ 8 by decide)
      exact add_le_add (by simpa only [pow_one] using hpow) le_rfl

/-- A polynomial-budget inverse theorem and stretched-exponential
prime–Cramér orthogonality against the same tests imply the quantitative
prime Gowers estimate. The exponent is chosen after the inverse loss. -/
theorem gowersUniformityEstimate_of_inverse_and_correlation (d A : ℕ)
    (tests : ℕ → ℝ → Set (ℤ → ℂ))
    (hinverse : IntervalCorrelationInverse d.succ tests)
    (horthogonal : ∃ b M : ℝ, 0 < b ∧ 0 < M ∧ ∀ᶠ X : ℕ in atTop,
      ∀ p : ℝ, p ≤ Real.log (X : ℝ) ^ b → ∀ F ∈ tests X p,
        intervalCorrelation X (strictVonMangoldtCramerDifference X) F ≤
          M * Real.exp (-(Real.log (X : ℝ) ^ b))) :
    GowersUniformityEstimate d.succ A := by
  obtain ⟨C, hC, hinverse⟩ := hinverse
  obtain ⟨b, M, hb, hM, horthogonal⟩ := horthogonal
  obtain ⟨B, hB, hbounded⟩ := eventually_abs_strictVonMangoldtCramerDifference
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  let r := b / (4 * C)
  have hr : 0 < r := div_pos hb (by positivity)
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hS := (tendsto_rpow_atTop hr).comp hlog
  have hT := (tendsto_rpow_atTop (show 0 < b / 2 by positivity)).comp hlog
  apply gowersUniformityEstimate_of_vonMangoldt_strict_cramer d A one_pos hr
  filter_upwards [horthogonal, hbounded, hlog.eventually_ge_atTop B,
    hS.eventually_ge_atTop (max (C : ℝ) 3), hT.eventually_ge_atTop (max 2 M),
    eventually_log_pow_le_exp_log_rpow 9 hr,
    eventually_ge_atTop (2 * (d.succ + 1))] with X horthogonal hbounded hL hS hT hpoly hX
  let L := Real.log (X : ℝ)
  let S := L ^ r
  let T := L ^ (b / 2)
  let p := 2 * S
  let R := B * L ^ (8 : ℕ)
  let w := strictVonMangoldtCramerDifference X
  have hLpos : 0 < L := zero_lt_one.trans_le (hB.trans hL)
  have hR : 1 ≤ R := by
    apply one_le_mul_of_one_le_of_one_le hB
    exact one_le_pow₀ (hB.trans hL)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRle : R ≤ Real.exp S := by
    refine (mul_le_mul_of_nonneg_right hL (pow_nonneg hLpos.le 8)).trans ?_
    simpa only [pow_succ'] using hpoly
  have hSthree : 3 ≤ S := (le_max_right (C : ℝ) 3).trans hS
  have hSC : (C : ℝ) ≤ S := (le_max_left (C : ℝ) 3).trans hS
  have hTtwo : 2 ≤ T := (le_max_left (2 : ℝ) M).trans hT
  have hTM : M ≤ T := (le_max_right (2 : ℝ) M).trans hT
  have hTsq : T ^ (2 : ℕ) = L ^ b := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast hLpos.le]
    norm_num
  have hbudget : (p + C) ^ C ≤ T := by
    calc
      _ ≤ (S ^ (2 : ℕ)) ^ C := by
        apply pow_le_pow_left₀ (by dsimp [p]; linarith)
        calc
          p + C ≤ 3 * S := by dsimp [p]; linarith
          _ ≤ S ^ (2 : ℕ) := by nlinarith
      _ = T := by
        dsimp only [S, T]
        rw [← pow_mul, ← Real.rpow_mul_natCast hLpos.le]
        congr 1
        push_cast
        dsimp [r]
        field_simp
        norm_num
  have hdecay : M * Real.exp (-(L ^ b)) < Real.exp (-T) := by
    calc
      _ < Real.exp T * Real.exp (-(L ^ b)) := by
        apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
        exact hTM.trans_lt (lt_of_lt_of_le (by linarith) (Real.add_one_le_exp T))
      _ = Real.exp (T - L ^ b) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [← hTsq]; nlinarith)
  have hnorm : intervalGowersNorm d.succ X w ≤ Real.exp (-S) := by
    have hscaled : intervalGowersNorm d.succ X (fun n => R⁻¹ * w n) < Real.exp (-p) := by
      by_contra! hlarge
      have hcap (n : ℤ) (hn : n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ))) :
          |R⁻¹ * w n| ≤ 1 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hRpos), ← div_eq_inv_mul]
        exact (div_le_one hRpos).mpr (hbounded n hn)
      obtain ⟨F, hF, hcorrelation⟩ := hinverse X (by omega) p (by dsimp [p]; linarith)
        (fun n => R⁻¹ * w n) hcap hlarge
      rw [intervalCorrelation_mul_const X R⁻¹ (inv_nonneg.mpr hRpos.le)] at hcorrelation
      have hu := horthogonal _ (hbudget.trans (by rw [← hTsq]; nlinarith)) F hF
      have hge := (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hcorrelation
      have hupper : R⁻¹ * intervalCorrelation X w F ≤ M * Real.exp (-(L ^ b)) := by
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hu
        exact (inv_le_one₀ hRpos).mpr hR
      exact (not_lt_of_ge (hge.trans hupper)) hdecay
    rw [intervalGowersNorm_mul_const d X R⁻¹ (inv_nonneg.mpr hRpos.le), ← div_eq_inv_mul] at hscaled
    calc
      _ ≤ Real.exp (-p) * R := (div_lt_iff₀ hRpos).mp hscaled |>.le
      _ ≤ Real.exp (-p) * Real.exp S := mul_le_mul_of_nonneg_left hRle (Real.exp_pos _).le
      _ = Real.exp (-S) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [p]
        ring
  have hunitNonneg : 0 ≤ intervalCubeSum d.succ X (fun _ => 1) := by
    rw [intervalCubeSum_one_eq_card]
    positivity
  have hunitPos : 0 < intervalCubeSum d.succ X (fun _ => 1) := by
    by_contra! he
    have hzero := le_antisymm he hunitNonneg
    have hh := intervalCubeSum_one_ge (d := d.succ) hX
    rw [hzero, mul_zero] at hh
    exact (not_le_of_gt (pow_pos (by exact_mod_cast (show 0 < X by omega) : (0 : ℝ) < X) _)) hh
  have hnormNonneg : 0 ≤ intervalGowersNorm d.succ X w :=
    Real.rpow_nonneg (div_nonneg (intervalCubeSum_succ_nonneg d X w) hunitNonneg) _
  have hpows := pow_le_pow_left₀ hnormNonneg hnorm (2 ^ d.succ : ℕ)
  rw [intervalGowersNorm_pow, ← Real.exp_nat_mul] at hpows
  have hlast : Real.exp ((2 ^ d.succ : ℕ) * -S) ≤ Real.exp (-S) := by
    apply Real.exp_le_exp.mpr
    have hm : (1 : ℝ) ≤ (2 ^ d.succ : ℕ) := by exact_mod_cast Nat.one_le_pow d.succ 2 (by decide)
    nlinarith
  change intervalCubeSum d.succ X w ≤ (1 * Real.exp (-S)) * _
  simpa only [one_mul] using (div_le_iff₀ hunitPos).mp (hpows.trans hlast)

end PrimeUniformity
