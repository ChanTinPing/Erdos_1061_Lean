module

public import PrimeUniformity.CramerTypeI
public import PrimeUniformity.TypeI
public import PrimeUniformity.Vaughan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- A test sum on a set of positive integers along multiples of `d`. -/
noncomputable def divisorCorrelation (A : Finset ℕ) (F : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ A.filter (d ∣ ·), F n

/-- Partial summation bounds the logarithmically weighted Type I term
using unweighted prefixes of the same multiplicative fiber. -/
theorem norm_log_divisorCorrelation_le {X d : ℕ} (hd : 0 < d) (hdX : d ≤ X)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) {B : ℝ}
    (hprefix : ∀ k ≤ X / d, ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖ ≤ B) :
    ‖divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d‖ ≤
      2 * Real.log ((X / d : ℕ) : ℝ) * B := by
  let M := X / d
  let S := A.filter (d ∣ ·)
  let w (k : ℕ) := Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)
  have hM : 0 < M := Nat.div_pos hdX hd
  have hdiv (n : ℕ) (hn : n ∈ S) : 0 < n / d ∧ n / d ≤ M := by
    have ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
    have ⟨hn₀, hnX⟩ := Finset.mem_Ioc.mp (hA hnA)
    exact ⟨Nat.div_pos (Nat.le_of_dvd hn₀ hnd) hd, Nat.div_le_div_right hnX⟩
  have hpref (k : ℕ) :
      (∑ n ∈ S, if n / d ≤ k then F n else 0) =
        divisorCorrelation (A.filter (· ≤ d * k)) F d := by
    rw [← Finset.sum_filter, divisorCorrelation]
    congr 1
    ext n
    simp only [S, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, hnd⟩, hk⟩
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hnd
      exact ⟨⟨hn, hmul ▸ Nat.mul_le_mul_left d hk⟩, hnd⟩
    · rintro ⟨⟨hn, hk⟩, hnd⟩
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hnd
      rw [← hmul] at hk
      exact ⟨⟨hn, hnd⟩, Nat.le_of_mul_le_mul_left hk hd⟩
  have hfull : ‖∑ n ∈ S, F n‖ ≤ B := by
    have h := hprefix M le_rfl
    rw [← hpref] at h
    convert h using 2
    exact Finset.sum_congr rfl fun n hn => (if_pos (hdiv n hn).2).symm
  have hexpand :
      divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d =
        (Real.log (M : ℝ) : ℂ) * (∑ n ∈ S, F n) -
          ∑ k ∈ Finset.Ico 1 M, (w k : ℂ) *
            divisorCorrelation (A.filter (· ≤ d * k)) F d := by
    change (∑ n ∈ S, (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) = _
    calc
      _ = ∑ n ∈ S, ((Real.log (M : ℝ) : ℂ) * F n -
          ∑ k ∈ Finset.Ico 1 M, (w k : ℂ) * (if n / d ≤ k then F n else 0)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [log_nat_eq_prefix_sum (hdiv n hn).1 (hdiv n hn).2,
          Complex.ofReal_sub, Complex.ofReal_sum, sub_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : n / d ≤ k <;> simp [hk, w]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.mul_sum, hpref]
  rw [hexpand]
  calc
    _ ≤ ‖(Real.log (M : ℝ) : ℂ) * (∑ n ∈ S, F n)‖ +
        ‖∑ k ∈ Finset.Ico 1 M, (w k : ℂ) *
          divisorCorrelation (A.filter (· ≤ d * k)) F d‖ := norm_sub_le _ _
    _ ≤ |Real.log (M : ℝ)| * B + ∑ k ∈ Finset.Ico 1 M, |w k| * B := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hfull (abs_nonneg _)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hprefix k (Finset.mem_Ico.mp hk).2.le) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← add_mul, log_prefix_coeff_l1 M hM]

private theorem cramerTruncated_correlation (A : Finset ℕ) (F : ℕ → ℂ) (Q D : ℕ) :
    (∑ n ∈ A, (cramerTruncatedWeight Q D n : ℂ) * F n) =
      ∑ d ∈ Finset.Icc 1 D, (cramerTypeICoefficient Q d : ℂ) * divisorCorrelation A F d := by
  simp only [cramerTruncatedWeight_eq_typeI, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [divisorCorrelation, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : d ∣ n <;> simp [h]

private theorem sum_bilinear_eq_divisorCorrelation (X : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Ioc 0 X) (a b F : ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc 0 X, ∑ m ∈ Finset.Ioc 0 X,
      if d * m ∈ A then a d * b m * F (d * m) else 0) =
      ∑ d ∈ Finset.Ioc 0 X, a d * divisorCorrelation A (fun n => b (n / d) * F n) d := by
  apply Finset.sum_congr rfl
  intro d hd
  have hd₀ := (Finset.mem_Ioc.mp hd).1
  simp only [divisorCorrelation, Finset.mul_sum, ← Finset.sum_filter]
  refine Finset.sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).2, dvd_mul_right d m⟩
  · intro m _ k _ h
    exact Nat.eq_of_mul_eq_mul_left hd₀ h
  · intro n hn
    obtain ⟨hnA, k, rfl⟩ := Finset.mem_filter.mp hn
    obtain ⟨hkpos, hkX⟩ := Finset.mem_Ioc.mp (hA hnA)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hkpos)
    have hk' : k ≤ X := (Nat.le_mul_of_pos_left k hd₀).trans hkX
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hk, hk'⟩, hnA⟩, rfl⟩
  · intro m _
    rw [Nat.mul_div_cancel_left m hd₀, mul_assoc]

/-- Multiplying the truncation error by a one-bounded test preserves its L¹ bound. -/
theorem norm_cramerTruncation_correlation_le {X Q D : ℕ}
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) :
    ‖∑ n ∈ A, ((cramerTruncatedWeight Q D n - cramerWeight Q n : ℝ) : ℂ) * F n‖ ≤
      ∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n| := by
  refine (norm_sum_le _ _).trans ?_
  trans ∑ n ∈ A, |cramerWeight Q n - cramerTruncatedWeight Q D n|
  · apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hF n hn) (abs_nonneg _)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => abs_nonneg _)

/-- The bilinear term in Vaughan's decomposition, with the original
test support applied to the product of the two factors. -/
noncomputable def vaughanTypeIICorrelation (X U V : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc U X, ∑ m ∈ Finset.Ioc V X,
    if d * m ∈ A then (ArithmeticFunction.moebius d : ℂ) *
      (vaughanTypeIIRight V m : ℂ) * F (d * m) else 0

/-- The exact Vaughan and truncated Cramér decomposition on an arbitrary
subset of the positive interval. Restricting the test to a progression
preserves the product cutoff in the Type II term. -/
theorem prime_cramerTruncated_correlation (X U V Q D : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) :
    (∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n - cramerTruncatedWeight Q D n : ℝ) : ℂ) *
      F n) =
      (∑ d ∈ Finset.Ioc 0 (min X U), (ArithmeticFunction.moebius d : ℂ) *
        divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d) +
      (∑ n ∈ A.filter (· ≤ V), (ArithmeticFunction.vonMangoldt n : ℂ) * F n) -
      (∑ d ∈ Finset.Ioc 0 (min X (U * V)), (vaughanTypeICoefficient U V d : ℂ) *
        divisorCorrelation A F d) +
      vaughanTypeIICorrelation X U V A F -
      ∑ d ∈ Finset.Icc 1 D, (cramerTypeICoefficient Q d : ℂ) * divisorCorrelation A F d := by
  let M : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  let Λ : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let corr (a : ArithmeticFunction ℝ) := ∑ n ∈ A, (a n : ℂ) * F n
  have hsplit :
      (∑ n ∈ A, ((Λ n - cramerTruncatedWeight Q D n : ℝ) : ℂ) * F n) =
        corr (arithmeticLowCutoff U M * ArithmeticFunction.log) +
        corr (arithmeticLowCutoff V Λ) - corr (vaughanTypeICoefficient U V * Z) +
        corr (arithmeticHighCutoff U M * vaughanTypeIIRight V) -
        ∑ n ∈ A, (cramerTruncatedWeight Q D n : ℂ) * F n := by
    have h (n : ℕ) := congrArg (fun a : ArithmeticFunction ℝ => a n) (vonMangoldt_eq_vaughan U V)
    simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply] at h
    simp only [corr, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← add_mul, ← sub_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_sub]
    exact Finset.sum_congr rfl fun n _ => by
      simp only [Λ, M, Z, sub_eq_add_neg]
      rw [← h n]
  have hconv (a b : ArithmeticFunction ℝ) :
      corr (a * b) = ∑ d ∈ Finset.Ioc 0 X, ∑ m ∈ Finset.Ioc 0 X,
        if d * m ∈ A then (a d : ℂ) * (b m : ℂ) * F (d * m) else 0 :=
    sum_map_convolution_eq_bilinear Complex.ofRealHom X A hA a b F
  rw [hsplit, cramerTruncated_correlation]
  congr 1
  congr 1
  · congr 1
    · congr 1
      · rw [hconv, sum_bilinear_eq_divisorCorrelation X A hA]
        refine (Finset.sum_subset (s₁ := Finset.Ioc 0 (min X U)) (fun d hd => Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hd).1, ((Finset.mem_Ioc.mp hd).2).trans (min_le_left X U)⟩)
          (fun d hd hdu => ?_)).symm.trans ?_
        · have hu : ¬ d ≤ U := fun h => hdu (Finset.mem_Ioc.mpr
            ⟨(Finset.mem_Ioc.mp hd).1, le_min (Finset.mem_Ioc.mp hd).2 h⟩)
          simp [arithmeticLowCutoff_apply, hu]
        · apply Finset.sum_congr rfl
          intro d hd
          have hu := ((Finset.mem_Ioc.mp hd).2).trans (min_le_right X U)
          simp [arithmeticLowCutoff_apply, hu, ArithmeticFunction.log_apply, M]
      · simp only [corr, Λ, Finset.sum_filter, arithmeticLowCutoff_apply]
        exact Finset.sum_congr rfl fun n _ => by split <;> simp_all
    · rw [hconv, sum_bilinear_eq_divisorCorrelation X A hA]
      refine (Finset.sum_subset (s₁ := Finset.Ioc 0 (min X (U * V))) (fun d hd => Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hd).1, ((Finset.mem_Ioc.mp hd).2).trans (min_le_left X (U * V))⟩)
        (fun d hd hdUV => ?_)).symm.trans ?_
      · have hUV : U * V < d := by
          by_contra! h
          exact hdUV (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hd).1, le_min (Finset.mem_Ioc.mp hd).2 h⟩)
        simp [vaughanTypeICoefficient_eq_zero_of_cutoff_lt hUV]
      · apply Finset.sum_congr rfl
        intro d hd
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        have hdiv := (Finset.mem_filter.mp hn).2
        have hn₀ := (Finset.mem_Ioc.mp (hA (Finset.mem_filter.mp hn).1)).1
        have hm : n / d ≠ 0 := by
          intro h
          have heq := Nat.div_mul_cancel hdiv
          rw [h, zero_mul] at heq
          exact hn₀.ne' heq.symm
        simp [Z, ArithmeticFunction.zeta_apply, hm]
  · rw [hconv, vaughanTypeIICorrelation]
    have subsetIoc (a : ℕ) : Finset.Ioc a X ⊆ Finset.Ioc 0 X :=
      fun _ hd => Finset.mem_Ioc.mpr ⟨(Nat.zero_le a).trans_lt (Finset.mem_Ioc.mp hd).1,
        (Finset.mem_Ioc.mp hd).2⟩
    refine (Finset.sum_subset (subsetIoc U) (fun d hd hdU => ?_)).symm.trans ?_
    · have hU : ¬ U < d := fun h => hdU (Finset.mem_Ioc.mpr ⟨h, (Finset.mem_Ioc.mp hd).2⟩)
      simp [arithmeticHighCutoff_apply, hU]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [arithmeticHighCutoff_apply, if_pos (Finset.mem_Ioc.mp hd).1]
      refine (Finset.sum_subset (subsetIoc V) (fun m hm hmV => ?_)).symm.trans ?_
      · have hV : m ≤ V := by
          by_contra! h
          exact hmV (Finset.mem_Ioc.mpr ⟨h, (Finset.mem_Ioc.mp hm).2⟩)
        simp [vaughanTypeIIRight_eq_zero_of_le_cutoff hV]
      · simp [M]

/-- The exact finite decomposition incurs only the existing Cramér
truncation error, uniformly for any one-bounded test and any support. -/
theorem eventually_prime_cramer_correlation_truncation :
    ∀ᶠ X : ℕ in atTop, ∀ (A : Finset ℕ), A ⊆ Finset.Ioc 0 X →
      ∀ F : ℕ → ℂ, (∀ n ∈ A, ‖F n‖ ≤ 1) →
        ‖(∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n -
          cramerWeight (strictPrimeUniformityCutoff X) n : ℝ) : ℂ) * F n) -
          ∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n -
            cramerTruncatedWeight (strictPrimeUniformityCutoff X) X.sqrt n : ℝ) : ℂ) * F n‖ ≤
          (X : ℝ) * Real.exp (-(Real.sqrt (Real.log (X : ℝ)) / 8)) := by
  filter_upwards [eventually_cramerTypeI_l1_error] with X hX A hA F hF
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, ← Complex.ofReal_sub, sub_sub_sub_cancel_left]
  exact (norm_cramerTruncation_correlation_le A hA F hF).trans hX

end PrimeUniformity
