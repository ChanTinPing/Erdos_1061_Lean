module

public import PrimeUniformity.CramerDecomposition
public import PrimeUniformity.CramerCutoff
public import PrimeUniformity.PrimePowers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- Every cutoff at least the square root of the interval length gives the
same stretched-exponential upper bound for the Cramér truncation error. -/
theorem eventually_cramerTypeI_l1_error_of_sqrt_le :
    ∀ᶠ X : ℕ in atTop, ∀ D : ℕ, X.sqrt ≤ D →
      (∑ n ∈ Finset.Ioc 0 X,
        |cramerWeight (strictPrimeUniformityCutoff X) n -
          cramerTruncatedWeight (strictPrimeUniformityCutoff X) D n|) ≤
        (X : ℝ) * Real.exp (-(Real.sqrt (Real.log (X : ℝ)) / 8)) := by
  let E := Real.exp 1
  let C := 1 / Real.log 2 + 2
  let K := 1 + E * C
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht₂ : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (2 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp ht
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop 4,
    ht₂.eventually_ge_atTop (8 * K)] with X hX hL hK
  intro D' hDD'
  let L := Real.log (X : ℝ)
  let t := L ^ (1 / 10 : ℝ)
  let R := Real.sqrt L
  let s := R⁻¹
  let Q := strictPrimeUniformityCutoff X
  let D := X.sqrt
  let N := Nat.log 2 Q + 1
  change 4 ≤ L at hL
  have hLpos : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hx : 0 < (X : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hX
  have hR : 0 < R := Real.sqrt_pos.mpr hLpos
  have hS : 0 ≤ s := inv_nonneg.mpr hR.le
  have hRsq : R ^ (2 : ℕ) = L := Real.sq_sqrt hLpos.le
  have ht₁ : 1 ≤ t := Real.one_le_rpow hL₁ (by norm_num)
  have htR : t ≤ R := by
    rw [show R = L ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow L]
    exact Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
  have hQlo : 1 ≤ Q := by
    have he : (2 : ℝ) ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hceil : 2 ≤ ⌈Real.exp t⌉₊ := by
      exact_mod_cast he.trans (Nat.le_ceil (Real.exp t))
    change 1 ≤ ⌈Real.exp t⌉₊ - 1
    omega
  have hQhi : (Q : ℝ) ≤ Real.exp t := by
    have hh : Q ≤ primeUniformityCutoff X := strictPrimeUniformityCutoff_le X
    exact (show (Q : ℝ) ≤ (primeUniformityCutoff X : ℝ) by exact_mod_cast hh).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hD : 0 < D := Nat.sqrt_pos.mpr (Nat.zero_lt_one.trans_le hX)
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDlog : L / 4 ≤ Real.log (D : ℝ) := by
    have hsq : (X : ℝ) ≤ ((D : ℝ) + 1) ^ (2 : ℕ) := by
      exact_mod_cast (Nat.lt_succ_sqrt' X).le
    have he' := Real.log_le_log hx hsq
    rw [Real.log_pow] at he'
    norm_num at he'
    have htwo : (D : ℝ) + 1 ≤ 2 * (D : ℝ) := by
      have h : (1 : ℝ) ≤ D := by exact_mod_cast hD
      linarith
    have hh := Real.log_le_log (by positivity : 0 < (D : ℝ) + 1) htwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDR.ne'] at hh
    have hlog₂ : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith only [he', hh, hL, hlog₂]
  have hDec : ((D : ℝ) ^ s)⁻¹ ≤ Real.exp (-(R / 4)) := by
    rw [Real.rpow_def_of_pos hDR, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hDlog hS
    have hRs : L / 4 * s = R / 4 := by
      dsimp only [s]
      rw [← hRsq]
      field_simp [hR.ne']
    rw [hRs] at hh
    rw [mul_comm (Real.log (D : ℝ)) s]
    linarith
  have hRecip : (∑ p ∈ cramerPrimeSet Q, (1 : ℝ) / (p : ℝ)) ≤ C * t := by
    have hQpow : Q ≤ (2 : ℕ) ^ N := (Nat.lt_pow_succ_log_self (by decide) Q).le
    have hsub : cramerPrimeSet Q ⊆ Finset.range ((2 : ℕ) ^ N + 1) := by
      intro p hp
      have hpQ := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_range.mpr (by omega)
    have hsum := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => show 0 ≤ (1 : ℝ) / (p : ℝ) by positivity)).trans
      (harmonic_sum_pow_two_le N)
    have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogQ : Real.log (Q : ℝ) ≤ t := by
      have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hQlo)
      simpa only [Real.log_exp] using Real.log_le_log hQpos hQhi
    have hN := (log_nat_cast_le_log_div_log_two hQlo).trans
      (div_le_div_of_nonneg_right hlogQ hlog₂.le)
    refine hsum.trans ?_
    dsimp [N, C]
    push_cast
    have he : (1 / Real.log 2 + 2) * t = t / Real.log 2 + 2 * t := by ring
    rw [he]
    linarith
  have hProd : (∏ p ∈ cramerPrimeSet Q, (1 + (p : ℝ) ^ (s - 1))) ≤
      Real.exp (E * (C * t)) := by
    refine le_trans ?_ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hRecip (Real.exp_pos _).le))
    rw [Finset.mul_sum, Real.exp_sum]
    first
    | apply Finset.prod_le_prod₀
    | apply Finset.prod_le_prod
    · exact fun p _ => add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    · intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hpQ : p ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hplog : Real.log (p : ℝ) ≤ t := by
        have hpr : (p : ℝ) ≤ Real.exp t :=
          (show (p : ℝ) ≤ (Q : ℝ) by exact_mod_cast hpQ).trans hQhi
        simpa only [Real.log_exp] using Real.log_le_log hpPos hpr
      have hpE : (p : ℝ) ^ s ≤ E := by
        rw [Real.rpow_def_of_pos hpPos]
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ R * s := mul_le_mul_of_nonneg_right (hplog.trans htR) hS
          _ = 1 := mul_inv_cancel₀ hR.ne'
      have hb : (p : ℝ) ^ (s - 1) ≤ E * (1 / (p : ℝ)) := by
        rw [Real.rpow_sub hpPos, Real.rpow_one, ← mul_div_assoc, mul_one]
        exact div_le_div_of_nonneg_right hpE hpPos.le
      linarith only [hb, Real.add_one_le_exp (E * (1 / (p : ℝ)))]
  have hrate : K * t ≤ R / 8 := by
    have heq : R = (L ^ (2 / 5 : ℝ)) * t := by
      rw [show R = L ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow L]
      dsimp only [t]
      rw [← Real.rpow_add hLpos]
      norm_num
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    rw [heq, show K * t * 8 = (8 * K) * t by ring]
    exact mul_le_mul_of_nonneg_right hK (zero_le_one.trans ht₁)
  have hSubset : (cramerPrimeProduct Q).divisors.filter (D' < ·) ⊆
      (cramerPrimeProduct Q).divisors.filter (D < ·) :=
    fun _ hd => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hd).1, hDD'.trans_lt (Finset.mem_filter.mp hd).2⟩
  have hTail := (Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (f := fun d : ℕ => (d : ℝ)⁻¹) (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))).trans
    ((cramerDivisorTail_le_rankin Q D hD s hS).trans
    (mul_le_mul hDec hProd (Finset.prod_nonneg fun p _ =>
      add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg p) _))
      (Real.exp_pos _).le))
  have hNorm := (cramerNormalization_le_cutoff hQlo).trans hQhi
  refine (sum_abs_cramerWeight_sub_truncated_le Q D' X).trans ?_
  calc
    _ ≤ Real.exp t * ((X : ℝ) * (Real.exp (-(R / 4)) * Real.exp (E * (C * t)))) :=
      mul_le_mul hNorm (mul_le_mul_of_nonneg_left hTail hx.le)
        (mul_nonneg hx.le (Finset.sum_nonneg fun _ _ => by positivity)) (Real.exp_pos _).le
    _ = (X : ℝ) * Real.exp (K * t - R / 4) := by
      rw [show K * t - R / 4 = t + (-(R / 4) + E * (C * t)) by dsimp [K]; ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx.le

/-- Truncating the Cramér divisor expansion at the square root of the
interval length leaves a stretched-exponentially small total error. -/
theorem eventually_cramerTypeI_l1_error :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Finset.Ioc 0 X,
        |cramerWeight (strictPrimeUniformityCutoff X) n -
          cramerTruncatedWeight (strictPrimeUniformityCutoff X) X.sqrt n|) ≤
        (X : ℝ) * Real.exp (-(Real.sqrt (Real.log (X : ℝ)) / 8)) :=
  eventually_cramerTypeI_l1_error_of_sqrt_le.mono fun X h => h X.sqrt le_rfl

end PrimeUniformity
