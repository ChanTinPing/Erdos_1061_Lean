module

public import PrimeUniformity.Bilinear
public import PrimeUniformity.PrimeCorrelation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators ComplexConjugate

private theorem norm_sum_mul_le_budget (s t : Finset ℕ) (hst : s ⊆ t)
    (a f : ℕ → ℂ) (b : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n ∈ t, 0 ≤ b n) (ha : ∀ n ∈ s, ‖a n‖ ≤ C)
    (hf : ∀ n ∈ s, ‖f n‖ ≤ b n) :
    ‖∑ n ∈ s, a n * f n‖ ≤ C * ∑ n ∈ t, b n := by
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ s, C * b n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (ha n hn) (hf n hn) (norm_nonneg _) hC
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hst
        (fun n hn _ => hb n hn)) hC

/-- The three Type I terms share a budget for the unweighted prefixes.
This leaves only a Type II correlation, the low von Mangoldt cutoff and
the explicit Cramér truncation error. -/
theorem norm_prime_cramer_correlation_le {X U V Q D : ℕ} (hX : 0 < X)
    (hU : U ≤ D) (hUV : U * V ≤ D) (hD : D ≤ X)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ)
    (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) (b : ℕ → ℝ)
    (hI : ∀ d ∈ Finset.Ioc 0 D, ∀ k ≤ X / d,
      ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖ ≤ b d) :
    ‖∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n - cramerWeight Q n : ℝ) : ℂ) * F n‖ ≤
      (3 * Real.log (X : ℝ) + cramerNormalization Q) * (∑ d ∈ Finset.Ioc 0 D, b d) +
        (V : ℝ) * Real.log (X : ℝ) + ‖vaughanTypeIICorrelation X U V A F‖ +
        ∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n| := by
  let B := Finset.Ioc 0 D
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hX)
  have hb (d : ℕ) (hd : d ∈ B) : 0 ≤ b d :=
    (norm_nonneg _).trans (hI d hd 0 (Nat.zero_le _))
  have hsub (E : ℕ) (hE : E ≤ D) : Finset.Ioc 0 (min X E) ⊆ B :=
    fun _ hd => Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hd).1, ((Finset.mem_Ioc.mp hd).2).trans ((min_le_right X E).trans hE)⟩
  have log_le {m : ℕ} (hm : 0 < m) (hmX : m ≤ X) : Real.log (m : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmX)
  have hfull (d : ℕ) (hd : d ∈ B) : ‖divisorCorrelation A F d‖ ≤ b d := by
    have heq : divisorCorrelation (A.filter (· ≤ d * (X / d))) F d = divisorCorrelation A F d := by
      unfold divisorCorrelation
      congr 1
      ext n
      simp only [Finset.mem_filter]
      refine ⟨fun h => ⟨h.1.1, h.2⟩, fun ⟨hn, hnd⟩ => ⟨⟨hn, ?_⟩, hnd⟩⟩
      rw [← Nat.mul_div_cancel' hnd]
      exact Nat.mul_le_mul_left d (Nat.div_le_div_right (Finset.mem_Ioc.mp (hA hn)).2)
    rw [← heq]
    exact hI d hd _ le_rfl
  have hfirst :
      ‖∑ d ∈ Finset.Ioc 0 (min X U), (ArithmeticFunction.moebius d : ℂ) *
        divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d‖ ≤
        (2 * L) * ∑ d ∈ B, b d := by
    have h := norm_sum_mul_le_budget _ B (hsub U hU)
      (fun d => (ArithmeticFunction.moebius d : ℂ))
      (fun d => divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d)
      (fun d => 2 * L * b d) (C := 1) zero_le_one
      (fun d hd => mul_nonneg (by positivity) (hb d hd))
      (fun d _ => by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d)))
      (fun d hd => by
        have ⟨hd₀, hdD⟩ := Finset.mem_Ioc.mp (hsub U hU hd)
        have hdX := hdD.trans hD
        refine (norm_log_divisorCorrelation_le hd₀ hdX A hA F (hI d (hsub U hU hd))).trans ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (log_le (Nat.div_pos hdX hd₀) (Nat.div_le_self _ _)) (by norm_num))
          (hb d (hsub U hU hd)))
    simpa only [one_mul, ← Finset.mul_sum] using h
  have hsmall :
      ‖∑ n ∈ A.filter (· ≤ V), (ArithmeticFunction.vonMangoldt n : ℂ) * F n‖ ≤ (V : ℝ) * L := by
    have hsub' : A.filter (· ≤ V) ⊆ Finset.Ioc 0 V :=
      fun n hn => Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp (hA (Finset.mem_filter.mp hn).1)).1, (Finset.mem_filter.mp hn).2⟩
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _n ∈ A.filter (· ≤ V), L := by
        apply Finset.sum_le_sum
        intro n hn
        have hnA := (Finset.mem_filter.mp hn).1
        obtain ⟨hn₀, hnX⟩ := Finset.mem_Ioc.mp (hA hnA)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc
          _ ≤ ArithmeticFunction.vonMangoldt n * 1 :=
            mul_le_mul_of_nonneg_left (hF n hnA) ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ _ := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le hn₀ hnX)
      _ ≤ ∑ _n ∈ Finset.Ioc 0 V, L :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun _ _ _ => hL)
      _ = _ := by simp [nsmul_eq_mul]
  have hsecond :
      ‖∑ d ∈ Finset.Ioc 0 (min X (U * V)), (vaughanTypeICoefficient U V d : ℂ) *
        divisorCorrelation A F d‖ ≤ L * ∑ d ∈ B, b d := by
    apply norm_sum_mul_le_budget _ B (hsub _ hUV) _ _ b hL hb _ (fun d hd => hfull d (hsub _ hUV hd))
    intro d hd
    obtain ⟨hd₀, hdX⟩ := Finset.mem_Ioc.mp hd
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_vaughanTypeICoefficient_le_log U V d).trans
      (log_le hd₀ (hdX.trans (min_le_left X (U * V))))
  have hcramer :
      ‖∑ d ∈ Finset.Icc 1 D, (cramerTypeICoefficient Q d : ℂ) * divisorCorrelation A F d‖ ≤
        cramerNormalization Q * ∑ d ∈ B, b d := by
    have heq : Finset.Icc 1 D = B := by
      ext d
      simp only [B, Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
    rw [heq]
    apply norm_sum_mul_le_budget B B (fun _ h => h) _ _ b (cramerNormalization_positive Q).le hb _ hfull
    intro d _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_cramerTypeICoefficient_le Q d
  let p := ∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n - cramerWeight Q n : ℝ) : ℂ) * F n
  let t := ∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n - cramerTruncatedWeight Q D n : ℝ) : ℂ) * F n
  have herr : ‖p - t‖ ≤ ∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n| := by
    dsimp only [p, t]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, ← Complex.ofReal_sub, sub_sub_sub_cancel_left]
    exact norm_cramerTruncation_correlation_le A hA F hF
  have ht : ‖t‖ ≤ (3 * L + cramerNormalization Q) * (∑ d ∈ B, b d) +
      (V : ℝ) * L + ‖vaughanTypeIICorrelation X U V A F‖ := by
    dsimp only [t]
    rw [prime_cramerTruncated_correlation X U V Q D A hA F]
    let I₁ := ∑ d ∈ Finset.Ioc 0 (min X U), (ArithmeticFunction.moebius d : ℂ) *
      divisorCorrelation A (fun n => (Real.log ((n / d : ℕ) : ℝ) : ℂ) * F n) d
    let I₂ := ∑ d ∈ Finset.Ioc 0 (min X (U * V)), (vaughanTypeICoefficient U V d : ℂ) *
      divisorCorrelation A F d
    let C := ∑ d ∈ Finset.Icc 1 D, (cramerTypeICoefficient Q d : ℂ) * divisorCorrelation A F d
    let S := ∑ n ∈ A.filter (· ≤ V), (ArithmeticFunction.vonMangoldt n : ℂ) * F n
    let II := vaughanTypeIICorrelation X U V A F
    have hV : ‖I₁ + S - I₂ + II - C‖ ≤ ‖I₁‖ + ‖S‖ + ‖I₂‖ + ‖II‖ + ‖C‖ := by
      calc
        _ ≤ ‖I₁ + S - I₂ + II‖ + ‖C‖ := norm_sub_le _ _
        _ ≤ ‖I₁ + S - I₂‖ + ‖II‖ + ‖C‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖I₁ + S‖ + ‖I₂‖ + ‖II‖ + ‖C‖ :=
          add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
        _ ≤ _ := add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    change ‖I₁ + S - I₂ + II - C‖ ≤ _
    calc
      _ ≤ ‖I₁‖ + ‖S‖ + ‖I₂‖ + ‖II‖ + ‖C‖ := hV
      _ ≤ (2 * L) * (∑ d ∈ B, b d) + (V : ℝ) * L + L * (∑ d ∈ B, b d) + ‖II‖ +
          cramerNormalization Q * (∑ d ∈ B, b d) :=
        add_le_add (add_le_add (add_le_add (add_le_add hfirst hsmall) hsecond) le_rfl) hcramer
      _ = _ := by ring
  change ‖p‖ ≤ _
  calc
    _ = ‖t + (p - t)‖ := by rw [add_sub_cancel]
    _ ≤ ‖t‖ + ‖p - t‖ := norm_add_le _ _
    _ ≤ _ := add_le_add ht herr

end PrimeUniformity
