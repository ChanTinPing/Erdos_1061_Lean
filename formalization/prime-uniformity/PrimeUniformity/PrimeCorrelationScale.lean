module

public import PrimeUniformity.TypeIPrefixes
public import PrimeUniformity.PrimeProgressionTests
public import PrimeUniformity.TypeIIProgressions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- A large strict prime correlation supported on one residue class forces
the class modulus to be small at the logarithmic budget of the test. -/
theorem eventually_progression_modulus_lt_exp_of_large_prime_correlation :
    ∀ᶠ X : ℕ in atTop, ∀ {q : ℕ}, 0 < q → ∀ (a : ZMod q) (F : ℤ → ℂ),
      (∀ n ∈ interval 1 (X : ℤ), ‖F n‖ ≤ 1) →
      (∀ n ∈ interval 1 (X : ℤ), (n : ZMod q) ≠ a → F n = 0) →
      ∀ p : ℝ, max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
      p ≤ Real.log (X : ℝ) ^ (1 / 20 : ℝ) →
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) F →
      (q : ℝ) < Real.exp (11 * p) := by
  obtain ⟨B, hB, hbounded⟩ := eventually_abs_strictVonMangoldtCramerDifference
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h95 := (tendsto_rpow_atTop (show (0 : ℝ) < 19 / 20 by norm_num)).comp hlog
  filter_upwards [hbounded, hlog.eventually_ge_atTop B, h95.eventually_ge_atTop 12,
    eventually_gt_atTop (0 : ℕ)] with X hbounded hLB hLpow hX
  intro q hq a F hF hsupport p hp₀ hpX hlarge
  let L := Real.log (X : ℝ)
  have hLp : 0 < L := zero_lt_one.trans_le (hB.trans hLB)
  have hp₂ := (le_max_left _ _).trans hp₀
  have hLexp : L ≤ Real.exp p :=
    (Real.log_le_iff_le_exp hLp).mp ((le_max_right _ _).trans hp₀)
  have hLbig : 12 * p ≤ L := calc
    _ ≤ 12 * L ^ (1 / 20 : ℝ) := mul_le_mul_of_nonneg_left hpX (by norm_num)
    _ ≤ L ^ (19 / 20 : ℝ) * L ^ (1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_right hLpow (by positivity)
    _ = L := by rw [← Real.rpow_add hLp, show (19 / 20 : ℝ) + 1 / 20 = 1 by norm_num,
      Real.rpow_one]
  have hw n (hn : n ∈ interval 1 (X : ℤ)) :
      |strictVonMangoldtCramerDifference X n| ≤ Real.exp (9 * p) := calc
    _ ≤ B * L ^ (8 : ℕ) := hbounded n hn
    _ ≤ L ^ (9 : ℕ) := by
      rw [pow_succ' L 8]
      exact mul_le_mul_of_nonneg_right hLB (pow_nonneg hLp.le 8)
    _ ≤ Real.exp p ^ (9 : ℕ) := pow_le_pow_left₀ hLp.le hLexp 9
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hhalf : Real.exp (-2 * p) ≤ Real.exp (-p) / 2 := by
    have hpExp : 2 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-2 * p) * Real.exp p :=
        mul_le_mul_of_nonneg_left hpExp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (9 * p) / (X : ℝ) ≤ Real.exp (-p) / 2 := by
    have hXr : (0 : ℝ) < X := Nat.cast_pos.mpr hX
    calc
      _ = Real.exp (9 * p - L) := by rw [Real.exp_sub, Real.exp_log hXr]
      _ ≤ Real.exp (-2 * p) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := hhalf
  by_contra! hqlarge
  have hsmallq : Real.exp (9 * p) / (q : ℝ) ≤ Real.exp (-p) / 2 := calc
    _ ≤ Real.exp (9 * p) / Real.exp (11 * p) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hqlarge
    _ = Real.exp (-2 * p) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := hhalf
  have hcorr := intervalCorrelation_residue_le hq a _ F (Real.exp_pos (9 * p)).le hw hF hsupport
  linarith only [hcorr, hsmallq, hsmall, hlarge]

/-- At the logarithmic budgets used in the step descent, the Vaughan
low cutoff and Cramér truncation are negligible. A large prime correlation
forces Type I or Type II at explicit exponential thresholds. -/
theorem eventually_prime_cramer_large_correlation_cases :
    ∀ᶠ X : ℕ in atTop, ∀ (U V D : ℕ), U ≤ D → U * V ≤ D → X.sqrt ≤ D → D ≤ X → V ≤ X.sqrt →
      ∀ (A : Finset ℕ), A ⊆ Finset.Ioc 0 X → ∀ F : ℕ → ℂ, (∀ n ∈ A, ‖F n‖ ≤ 1) →
      ∀ p : ℝ, max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
        p ≤ Real.log (X : ℝ) ^ (1 / 20 : ℝ) →
        (X : ℝ) * Real.exp (-p) <
          ‖∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n -
            cramerWeight (strictPrimeUniformityCutoff X) n : ℝ) : ℂ) * F n‖ →
        DenseTypeIPrefixes X D A F (Real.exp (-20 * p)) ∨
          ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
            (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A F‖ := by
  obtain ⟨B, hB, hbounded⟩ := eventually_abs_cramerWeight_le_log_pow
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h45 := (tendsto_rpow_atTop (show (0 : ℝ) < 9 / 20 by norm_num)).comp hlog
  have h95 := (tendsto_rpow_atTop (show (0 : ℝ) < 19 / 20 by norm_num)).comp hlog
  filter_upwards [hbounded, eventually_cramerTypeI_l1_error_of_sqrt_le,
    eventually_gt_atTop (0 : ℕ), hlog.eventually_ge_atTop (B + 3),
    hlog.eventually_ge_atTop (1 / Real.log 2 + 1),
    hlog.eventually_ge_atTop (8 * Real.log 8),
    h45.eventually_ge_atTop 24, h95.eventually_ge_atTop 12]
    with X hbounded htail hX hB3 hlog₂ hlog₈ h45 h95
  intro U V D hU hUV hD₂ hDX hV A hA F hF p hp₀ hpX hlarge
  let L := Real.log (X : ℝ)
  let Q := strictPrimeUniformityCutoff X
  let T := L ^ (1 / 20 : ℝ)
  let ε := Real.exp (-20 * p)
  let E := (X : ℝ) * Real.exp (-3 * p)
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp₀
  have hL₁ : 1 ≤ L := by linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hXp : 0 < (X : ℝ) := by exact_mod_cast hX
  have hLexp : L ≤ Real.exp p :=
    (Real.log_le_iff_le_exp hLp).mp ((le_max_right _ _).trans hp₀)
  have hcramerOne : cramerWeight Q 1 = cramerNormalization Q := by
    unfold cramerWeight
    apply if_pos
    intro d hd hdiv
    have hprime : d.Prime := (Finset.mem_filter.mp hd).2
    exact hprime.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)
  have hcramer : cramerNormalization Q ≤ B * L ^ (8 : ℕ) := by
    simpa only [hcramerOne, abs_of_nonneg (cramerNormalization_positive Q).le] using
      hbounded Q (strictPrimeUniformityCutoff_le X) 1
  have hcoef : 3 * L + cramerNormalization Q ≤ L ^ (9 : ℕ) := by
    have hpow : L ≤ L ^ (8 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ hL₁ (by decide : (1 : ℕ) ≤ 8)
    calc
      _ ≤ (B + 3) * L ^ (8 : ℕ) := by linarith
      _ ≤ _ := by rw [pow_succ' L 8]; exact mul_le_mul_of_nonneg_right hB3 (pow_nonneg hLp.le 8)
  have hbin : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ L ^ (2 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ L / Real.log 2 + L := add_le_add (log_nat_cast_le_log_div_log_two hX) hL₁
      _ = (1 / Real.log 2 + 1) * L := by ring
      _ ≤ _ := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hlog₂ hLp.le
  have hbinD : ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ L ^ (2 : ℕ) := by
    exact (show ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) by
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hDX) 1).trans hbin
  have hscale (a : ℕ) (ha : a ≤ 17) : L ^ a * ε * (X : ℝ) ≤ E := by
    calc
      _ ≤ Real.exp p ^ a * ε * (X : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hLp.le hLexp a) (Real.exp_pos _).le) hXp.le
      _ = (X : ℝ) * Real.exp (((a : ℝ) - 20) * p) := by
        dsimp only [ε]
        rw [← Real.exp_nat_mul, ← Real.exp_add, mul_comm _ (X : ℝ)]
        congr 1
        exact congrArg Real.exp (by ring)
      _ ≤ E := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have ha' : (a : ℝ) ≤ 17 := by exact_mod_cast ha
        nlinarith)) hXp.le
  have hTypeI : (3 * L + cramerNormalization Q) *
      (((Nat.log 2 D + 1 : ℕ) : ℝ) * (ε * X)) ≤ E := by
    calc
      _ ≤ L ^ (9 : ℕ) * (L ^ (2 : ℕ) * (ε * X)) :=
        mul_le_mul hcoef (mul_le_mul_of_nonneg_right hbinD (by positivity))
          (by positivity) (by positivity)
      _ = L ^ (11 : ℕ) * ε * X := by ring
      _ ≤ _ := hscale 11 (by decide)
  have hTypeII : ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 2 * ((X : ℝ) * ε) ≤ E := by
    calc
      _ ≤ (L ^ (2 : ℕ)) ^ 2 * ((X : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hbin 2) (by positivity)
      _ = L ^ (4 : ℕ) * ε * X := by ring
      _ ≤ _ := hscale 4 (by decide)
  have hT45 : 24 * T ≤ Real.sqrt L := by
    calc
      _ ≤ L ^ (9 / 20 : ℝ) * T := mul_le_mul_of_nonneg_right h45 (by positivity)
      _ = _ := by dsimp only [T]; rw [← Real.rpow_add hLp, Real.sqrt_eq_rpow]; norm_num
  have hT95 : 12 * T ≤ L := by
    calc
      _ ≤ L ^ (19 / 20 : ℝ) * T := mul_le_mul_of_nonneg_right h95 (by positivity)
      _ = _ := by dsimp only [T]; rw [← Real.rpow_add hLp]; norm_num
  have hTail : (∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n|) ≤ E :=
    (htail D hD₂).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hXp.le)
  have hL₄ : L ≤ Real.exp (L / 4) := by
    apply (Real.log_le_iff_le_exp hLp).mp
    have h := Real.log_le_sub_one_of_pos (show 0 < L / 8 by positivity)
    rw [show Real.log L = Real.log 8 + Real.log (L / 8) by
      rw [← Real.log_mul (by norm_num) (by positivity), show 8 * (L / 8) = L by ring]]
    linarith
  have hHalf : (V : ℝ) ≤ Real.exp (L / 2) := by
    have hv₂ : (V : ℝ) ^ (2 : ℕ) ≤ X := by exact_mod_cast Nat.le_sqrt'.mp hV
    have he₂ : Real.exp (L / 2) ^ (2 : ℕ) = (X : ℝ) := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (L / 2) = L by push_cast; ring, Real.exp_log hXp]
    by_contra! h
    exact (not_lt_of_ge hv₂) (he₂ ▸ (pow_lt_pow_left₀ h (Real.exp_pos _).le (by decide)))
  have hLow : (V : ℝ) * L ≤ E := by
    calc
      _ ≤ Real.exp (L / 2) * Real.exp (L / 4) :=
        mul_le_mul hHalf hL₄ hLp.le (Real.exp_pos _).le
      _ = Real.exp (3 * L / 4) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (L - 3 * p) := Real.exp_le_exp.mpr (by linarith)
      _ = E := by
        rw [show L - 3 * p = L + (-3 * p) by ring, Real.exp_add, Real.exp_log hXp]
  have hGap : E + E + E + E < (X : ℝ) * Real.exp (-p) := by
    have hp' : (4 : ℝ) < Real.exp (2 * p) := by linarith [Real.add_one_le_exp (2 * p)]
    calc
      _ = (X : ℝ) * (Real.exp (-3 * p) * 4) := by dsimp [E]; ring
      _ < (X : ℝ) * (Real.exp (-3 * p) * Real.exp (2 * p)) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hp' (Real.exp_pos _)) hXp
      _ = _ := by rw [← Real.exp_add, show -3 * p + 2 * p = -p by ring]
  apply prime_cramer_large_correlation_cases (Q := Q) (E := (X : ℝ) * ε)
    hX hU hUV hDX A hA F hF (Real.exp_pos _).le
  exact (add_le_add (add_le_add (add_le_add hTypeI hLow) hTypeII) hTail).trans_lt (hGap.trans hlarge)

/-- Apply the arithmetic alternative directly to a masked interval test.
The profile uses the conjugate of the test, as in the correlation convention. -/
theorem eventually_prime_cramer_large_residue_correlation_cases :
    ∀ᶠ X : ℕ in atTop, ∀ (U V D : ℕ), U ≤ D → U * V ≤ D → X.sqrt ≤ D → D ≤ X → V ≤ X.sqrt →
      ∀ (a b q r : ℕ), a ≤ b → b ≤ X → r < q →
      ∀ F : ℤ → ℂ, (∀ n, ‖F n‖ ≤ 1) → ∀ p : ℝ,
        max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
        p ≤ Real.log (X : ℝ) ^ (1 / 20 : ℝ) →
        Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X)
          (fun n => if n ∈ residueSlice ((a : ℤ) + 1) ((b - a : ℕ) : ℤ) (r : ZMod q)
            then F n else 0) →
        let A := (Finset.Ioc a b).filter (fun n => n % q = r)
        let G := fun n : ℕ => star (F n)
        DenseTypeIPrefixes X D A G (Real.exp (-20 * p)) ∨
          ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
            (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A G‖ := by
  filter_upwards [eventually_prime_cramer_large_correlation_cases,
    eventually_gt_atTop (0 : ℕ)] with X hcases hX
  intro U V D hU hUV hD₂ hDX hV a b q r hab hbX hr F hF p hp₀ hpX hlarge
  let A := (Finset.Ioc a b).filter (fun n => n % q = r)
  let G := fun n : ℕ => star (F n)
  have hA : A ⊆ Finset.Ioc 0 X := by
    intro n hn
    have ⟨han, hnb⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt han, hnb.trans hbX⟩
  have hG (n : ℕ) (_ : n ∈ A) : ‖G n‖ ≤ 1 := by
    simpa only [G, norm_star] using hF n
  apply hcases U V D hU hUV hD₂ hDX hV A hA G hG p hp₀ hpX
  rw [intervalCorrelation_residue_mask hab hbX hr] at hlarge
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have h := (lt_div_iff₀ hx).mp hlarge
  simpa only [mul_comm (Real.exp (-p)) (X : ℝ), G, A, strictVonMangoldtCramerDifference,
    vonMangoldtWeight, Int.toNat_natCast] using h

/-- A large Type II block has many actual rows and columns, including
when the dyadic ranges are clipped by the Vaughan cutoffs. -/
theorem large_prime_typeIIBlock_card_product {X U V i j : ℕ} (hX : 1 < X)
    (A : Finset ℕ) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1)
    {p : ℝ} (hp : Real.log (Real.log (X : ℝ)) ≤ p)
    (hlarge : (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A F‖) :
    (X : ℝ) * Real.exp (-21 * p) <
      ((dyadicFactorBlock U X i).card : ℝ) * ((dyadicFactorBlock V X j).card : ℝ) := by
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hLexp : Real.log (X : ℝ) ≤ Real.exp p := (Real.log_le_iff_le_exp hL).mp hp
  apply (mul_lt_mul_iff_left₀ (Real.exp_pos p)).mp
  calc
    ((X : ℝ) * Real.exp (-21 * p)) * Real.exp p = (X : ℝ) * Real.exp (-20 * p) := by
      rw [mul_assoc, ← Real.exp_add, show -21 * p + p = -20 * p by ring]
    _ < _ := hlarge
    _ ≤ _ := norm_vaughanTypeIIBlock_le_card_mul (by omega) A F hF
    _ ≤ _ := mul_le_mul_of_nonneg_left hLexp (by positivity)

/-- A Type II block at the threshold of the prime correlation alternative
has dense column pairs at an explicit exponential scale. The range of its
dyadic factor product retains the ambient length up to the stated loss. -/
theorem dense_columns_of_large_prime_typeIIBlock {X U V i j : ℕ} (hX : 1 < X)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1)
    {p : ℝ} (hp : max 2 (Real.log (Real.log (X : ℝ))) ≤ p)
    (hlarge : (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A F‖) :
    let s := dyadicFactorBlock U X i
    let t := dyadicFactorBlock V X j
    let K := vaughanTypeIIKernel A F
    let δ := Real.exp (-100 * p)
    (X : ℝ) * Real.exp (-21 * p) < (2 : ℝ) ^ i * 2 ^ j ∧ 2 ^ i * 2 ^ j ≤ X ∧
      δ * (t.card : ℝ) ^ 2 ≤
        (((t ×ˢ t).filter (fun u : ℕ × ℕ => δ * (s.card : ℝ) ≤
          ‖∑ d ∈ s, K d u.1 * star (K d u.2)‖)).card : ℝ) := by
  intro s t K δ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hp₂ := (le_max_left _ _).trans hp
  have hLexp : Real.log (X : ℝ) ≤ Real.exp p :=
    (Real.log_le_iff_le_exp hL).mp ((le_max_right _ _).trans hp)
  have hnorm : 0 < ‖vaughanTypeIIBlock X U V i j A F‖ :=
    (mul_pos hXp (Real.exp_pos _)).trans hlarge
  have hprod := dyadic_product_le_of_vaughanTypeIIBlock_ne_zero hA (norm_pos_iff.mp hnorm)
  have hcardscale : (X : ℝ) * Real.exp (-21 * p) < (s.card : ℝ) * (t.card : ℝ) :=
    large_prime_typeIIBlock_card_product hX A F hF ((le_max_right _ _).trans hp) hlarge
  have hs' : (s.card : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast card_dyadicFactorBlock_le U X i
  have ht' : (t.card : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast card_dyadicFactorBlock_le V X j
  have hscale := hcardscale.trans_le (mul_le_mul hs' ht' (Nat.cast_nonneg _) (by positivity))
  have hpos : (0 : ℝ) < (s.card : ℝ) * t.card := (mul_pos hXp (Real.exp_pos _)).trans hcardscale
  have hs : s.Nonempty := Finset.card_pos.mp
    (Nat.cast_pos.mp (pos_of_mul_pos_left hpos (Nat.cast_nonneg _)))
  have ht : t.Nonempty := Finset.card_pos.mp
    (Nat.cast_pos.mp (pos_of_mul_pos_right hpos (Nat.cast_nonneg _)))
  have hcards : (s.card : ℝ) * (t.card : ℝ) ≤ X := by
    exact_mod_cast (Nat.mul_le_mul (card_dyadicFactorBlock_le U X i)
      (card_dyadicFactorBlock_le V X j)).trans hprod
  have hexp : (Real.exp p) ^ (4 : ℕ) * (2 * δ) ≤ Real.exp (-20 * p) ^ (4 : ℕ) := by
    dsimp only [δ]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
    have htwo : 2 ≤ Real.exp (16 * p) := by linarith [Real.add_one_le_exp (16 * p)]
    calc
      _ = 2 * Real.exp (-96 * p) := by
        rw [show Real.exp (4 * p) * (2 * Real.exp (-(100 * p))) =
          2 * (Real.exp (4 * p) * Real.exp (-(100 * p))) by ring, ← Real.exp_add]
        congr 1
        exact congrArg Real.exp (by ring)
      _ ≤ Real.exp (16 * p) * Real.exp (-96 * p) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨hscale, hprod, ?_⟩
  have hlarge' : (s.card : ℝ) ^ 2 * ((t.card : ℝ) * Real.log (X : ℝ) ^ 2) ^ 2 *
      ((2 * δ) * (s.card : ℝ) ^ 2 * (t.card : ℝ) ^ 2) ≤
      ‖vaughanTypeIIBlock X U V i j A F‖ ^ 4 := by
    calc
      _ = ((s.card : ℝ) * (t.card : ℝ)) ^ 4 * (Real.log (X : ℝ) ^ 4 * (2 * δ)) := by ring
      _ ≤ (X : ℝ) ^ 4 * ((Real.exp p) ^ 4 * (2 * δ)) := by
        have hδ : 0 ≤ δ := (Real.exp_pos _).le
        gcongr
      _ ≤ (X : ℝ) ^ 4 * Real.exp (-20 * p) ^ 4 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((X : ℝ) * Real.exp (-20 * p)) ^ 4 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hlarge.le 4
  have hd := dense_vaughanTypeIIBlock_columns hX A F hF
    (δ := 2 * δ) (mul_nonneg (by norm_num) (Real.exp_pos _).le) hs ht hlarge'
  rw [show 2 * δ / 2 = δ by ring] at hd
  exact hd

/-- Produce the unmasked interval samples for the native Type II argument.
One row residue works for many dilation pairs, and the interval lengths
and normalized correlations are controlled on the same dyadic scale. -/
theorem exists_dense_typeII_progression_samples
    {X U V i j a b q z : ℕ} (hX : 1 < X) (hbX : b ≤ X) (hq : 0 < q)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {p : ℝ} (hp : max 2 (Real.log (Real.log (X : ℝ))) ≤ p)
    (hqp : (q : ℝ) ≤ Real.exp (11 * p))
    (hlarge : (X : ℝ) * Real.exp (-20 * p) <
      ‖vaughanTypeIIBlock X U V i j ((Finset.Ioc a b).filter (fun n => n % q = z)) f‖) :
    let t := dyadicFactorBlock V X j
    ∃ r < q, ∃ J ⊆ t ×ˢ t, Real.exp (-153 * p) * ((2 : ℝ) ^ j) ^ 2 ≤ (J.card : ℝ) ∧
      ∀ v ∈ J, ∃ lo hi : ℕ, lo ≤ hi ∧
        Real.exp (-121 * p) * ((2 : ℝ) ^ i / q) ≤ ((Finset.Icc lo hi).card : ℝ) ∧
        Real.exp (-111 * p) ≤
          ‖∑ x ∈ Finset.Icc lo hi, f (v.1 * (q * x + r)) * star (f (v.2 * (q * x + r)))‖ /
            ((Finset.Icc lo hi).card : ℝ) := by
  intro t
  let A := (Finset.Ioc a b).filter (fun n => n % q = z)
  let s := dyadicFactorBlock U X i
  let δ := Real.exp (-100 * p)
  let K := vaughanTypeIIKernel A f
  let T := (t ×ˢ t).filter (fun v : ℕ × ℕ => δ * (s.card : ℝ) ≤
    ‖∑ d ∈ s, K d v.1 * star (K d v.2)‖)
  have hA : A ⊆ Finset.Ioc 0 X := by
    intro n hn
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le a).trans_lt hl, hu.trans hbX⟩
  have hF n (_ : n ∈ A) := hf n
  obtain ⟨_, hwidth, hdense⟩ := dense_columns_of_large_prime_typeIIBlock hX A hA f hF hp hlarge
  have hcounts := large_prime_typeIIBlock_card_product hX A f hF ((le_max_right _ _).trans hp) hlarge
  have hD : 0 < (2 : ℝ) ^ i := by positivity
  have hM : 0 < (2 : ℝ) ^ j := by positivity
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hs' : (s.card : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast card_dyadicFactorBlock_le U X i
  have ht' : (t.card : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast card_dyadicFactorBlock_le V X j
  have hwidth' : (2 : ℝ) ^ i * (2 : ℝ) ^ j ≤ X := by exact_mod_cast hwidth
  have hvol := (mul_le_mul_of_nonneg_right hwidth' (Real.exp_pos (-21 * p)).le).trans hcounts.le
  have hs : Real.exp (-21 * p) * (2 : ℝ) ^ i ≤ s.card := by
    apply (mul_le_mul_iff_right₀ hM).mp
    calc
      _ = ((2 : ℝ) ^ i * (2 : ℝ) ^ j) * Real.exp (-21 * p) := by ring
      _ ≤ _ := (hvol.trans (mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg _))).trans_eq (mul_comm _ _)
  have ht : Real.exp (-21 * p) * (2 : ℝ) ^ j ≤ t.card := by
    apply (mul_le_mul_iff_left₀ hD).mp
    calc
      _ = ((2 : ℝ) ^ i * (2 : ℝ) ^ j) * Real.exp (-21 * p) := by ring
      _ ≤ _ := (hvol.trans (mul_le_mul_of_nonneg_right hs' (Nat.cast_nonneg _))).trans_eq (mul_comm _ _)
  have hCardS : (0 : ℝ) < s.card := (mul_pos (Real.exp_pos _) hD).trans_le hs
  let L := max (U + 1) (2 ^ i)
  let R := min X (2 ^ (i + 1) - 1)
  have hS : s = Finset.Icc L R := dyadicFactorBlock_eq_Icc U X i
  have hmask : Finset.Ioc a b = Finset.Icc (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  have hsubsum v (hv : v ∈ T) : δ * (s.card : ℝ) ≤
      ‖∑ d ∈ Finset.Icc L R,
        vaughanTypeIIKernel ((Finset.Icc (a + 1) b).filter (fun n => n % q = z)) f d v.1 *
          star (vaughanTypeIIKernel ((Finset.Icc (a + 1) b).filter (fun n => n % q = z)) f d v.2)‖ := by
    have h := (Finset.mem_filter.mp hv).2
    simpa only [K, A, hmask, hS] using h
  obtain ⟨r, hr, J, hJ, hsize, hsample⟩ :=
    exists_common_large_vaughan_dilation_subsums_with_support T L R (a + 1) b q z hq f hf
      (mul_pos (Real.exp_pos _) hCardS) hsubsum
  have hquot : Real.exp (-111 * p) ≤ δ / (q : ℝ) := by
    calc
      _ = δ / Real.exp (11 * p) := by
        dsimp only [δ]
        rw [← Real.exp_sub, show -100 * p - 11 * p = -111 * p by ring]
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hq' hqp
  have hJsize : Real.exp (-153 * p) * ((2 : ℝ) ^ j) ^ 2 ≤ (J.card : ℝ) := by
    calc
      _ = Real.exp (-111 * p) * (Real.exp (-21 * p) * (2 : ℝ) ^ j) ^ 2 := by
        rw [mul_pow, ← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        exact congrArg Real.exp (by norm_num; ring)
      _ ≤ (δ / (q : ℝ)) * (t.card : ℝ) ^ 2 :=
        mul_le_mul hquot (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (by positivity)
      _ = (δ * (t.card : ℝ) ^ 2) / (q : ℝ) := by ring
      _ ≤ (T.card : ℝ) / (q : ℝ) := div_le_div_of_nonneg_right hdense hq'.le
      _ ≤ _ := hsize
  refine ⟨r, hr, J, hJ.trans (Finset.filter_subset _ _), hJsize, ?_⟩
  intro v hv
  obtain ⟨_, _, lo, hi, hlohi, _, hlen, _, hmean⟩ := hsample v hv
  rw [← hS, show (δ * (s.card : ℝ) / (q : ℝ)) / s.card = δ / (q : ℝ) by
    field_simp [hCardS.ne', hq'.ne']] at hmean
  refine ⟨lo, hi, hlohi, ?_, hquot.trans hmean⟩
  calc
    _ = δ * (Real.exp (-21 * p) * (2 : ℝ) ^ i) / (q : ℝ) := by
      rw [← mul_assoc, show δ * Real.exp (-21 * p) = Real.exp (-121 * p) by
        dsimp only [δ]
        rw [← Real.exp_add, show -100 * p + -21 * p = -121 * p by ring], mul_div_assoc]
    _ ≤ _ := le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) hq'.le) hlen

/-- Fourth-root Vaughan cutoffs give enough row length whenever the
aggregate logarithmic budget fits inside a quarter of the ambient log. -/
theorem typeII_dilation_input_scale {X i q C : ℕ} (hX : 0 < X)
    (hi : X.sqrt.sqrt < 2 ^ (i + 1)) (hq : 0 < q) {p : ℝ}
    (hqp : (q : ℝ) ≤ Real.exp (11 * p))
    (hbudget : (111 * p + C) ^ C + 132 * p + Real.log 2 ≤ Real.log (X : ℝ) / 4) :
    Real.exp ((111 * p + C) ^ C) ≤ Real.exp (-121 * p) * ((2 : ℝ) ^ i / q) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hX' : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  have hrow_nat : X ≤ ((2 : ℕ) ^ (i + 1)) ^ 4 := by
    have h₂ := Nat.lt_succ_sqrt' X.sqrt
    have h₃ : X.sqrt.sqrt + 1 ≤ (2 : ℕ) ^ (i + 1) := hi
    calc
      _ ≤ (X.sqrt + 1) ^ 2 := (Nat.lt_succ_sqrt' X).le
      _ ≤ ((X.sqrt.sqrt + 1) ^ 2) ^ 2 := by gcongr; exact Nat.succ_le_of_lt h₂
      _ ≤ (((2 : ℕ) ^ (i + 1)) ^ 2) ^ 2 := by gcongr
      _ = _ := by rw [← pow_mul]
  have hrow : Real.exp (Real.log (X : ℝ) / 4) ≤ (2 : ℝ) * 2 ^ i := by
    have hrow_real : (X : ℝ) ≤ ((2 : ℝ) * 2 ^ i) ^ (4 : ℕ) := by
      rw [mul_comm (2 : ℝ), ← pow_succ]
      exact_mod_cast hrow_nat
    have h := Real.log_le_log hX' hrow_real
    rw [Real.log_pow] at h
    norm_num at h
    calc
      _ ≤ Real.exp (Real.log ((2 : ℝ) * 2 ^ i)) := Real.exp_le_exp.mpr (by linarith only [h])
      _ = _ := Real.exp_log (by positivity)
  have htotal : Real.exp ((111 * p + C) ^ C + 132 * p) ≤ (2 : ℝ) ^ i := by
    apply (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp
    calc
      2 * Real.exp ((111 * p + C) ^ C + 132 * p) =
          Real.exp ((111 * p + C) ^ C + 132 * p + Real.log 2) := by
        rw [Real.exp_add _ (Real.log 2), Real.exp_log (by norm_num : 0 < (2 : ℝ)), mul_comm]
      _ ≤ _ := (Real.exp_le_exp.mpr hbudget).trans hrow
  calc
    _ = Real.exp (-132 * p) * Real.exp ((111 * p + C) ^ C + 132 * p) := by
      rw [← Real.exp_add, show -132 * p + ((111 * p + C) ^ C + 132 * p) =
        (111 * p + C) ^ C by ring]
    _ ≤ Real.exp (-132 * p) * (2 : ℝ) ^ i := mul_le_mul_of_nonneg_left htotal (Real.exp_pos _).le
    _ = Real.exp (-121 * p) * ((2 : ℝ) ^ i / Real.exp (11 * p)) := by
      rw [mul_comm (Real.exp (-132 * p)), mul_comm (Real.exp (-121 * p)), div_mul_eq_mul_div,
        mul_div_assoc, ← Real.exp_sub, show -121 * p - 11 * p = -132 * p by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) hq' hqp) (Real.exp_pos _).le

private theorem eventually_power_budget_le_log_quarter (C : ℕ) (hC : 1 ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℝ, 2 ≤ p → p ^ C ≤ Real.sqrt (Real.log (X : ℝ)) →
      (a * p + C) ^ C + b * p + Real.log 2 ≤ Real.log (X : ℝ) / 4 := by
  let A : ℝ := (a + (C : ℝ)) ^ C + b
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have ht : Tendsto (fun X : ℕ => Real.sqrt (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually_ge_atTop (max 1 (4 * (A + Real.log 2)))]
    with X hX ht
  intro p hp hpX
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hX)
  have hT : 1 ≤ Real.sqrt L := (le_max_left _ _).trans ht
  have hTL : Real.sqrt L * (4 * (A + Real.log 2)) ≤ L := calc
    _ ≤ Real.sqrt L * Real.sqrt L :=
      mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) (Real.sqrt_nonneg _)
    _ = L := Real.mul_self_sqrt hL
  have hpC : p ≤ p ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p) hC
  have hbase : a * p + C ≤ (a + C) * p := by
    have hc : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hc (show 0 ≤ p - 1 by linarith)]
  calc
    _ ≤ ((a + (C : ℝ)) ^ C) * p ^ C + b * p ^ C + Real.log 2 := by
      rw [← mul_pow]
      gcongr
    _ = A * p ^ C + Real.log 2 := by dsimp only [A]; ring
    _ ≤ A * Real.sqrt L + Real.log 2 * Real.sqrt L := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpX hA)
        (le_mul_of_one_le_right (Real.log_nonneg (by norm_num)) hT)
    _ ≤ L / 4 := by linarith only [hTL]

/-- A fixed power budget controlled by the square root of the ambient log
fits the Type II row length condition for all sufficiently large X. -/
theorem eventually_typeII_dilation_input_scale (C : ℕ) (hC : 1 ≤ C) :
    ∀ᶠ X : ℕ in atTop, ∀ {i q : ℕ}, X.sqrt.sqrt < 2 ^ (i + 1) → 0 < q →
      ∀ p : ℝ, 2 ≤ p → p ^ C ≤ Real.sqrt (Real.log (X : ℝ)) →
      (q : ℝ) ≤ Real.exp (11 * p) →
      Real.exp ((111 * p + C) ^ C) ≤ Real.exp (-121 * p) * ((2 : ℝ) ^ i / q) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_power_budget_le_log_quarter C hC (a := 111) (b := 132) (by norm_num) (by norm_num)]
    with X hX hbudget
  intro i q hi hq p hp hpX hqp
  exact typeII_dilation_input_scale hX hi hq hqp (hbudget p hp hpX)

/-- The Type I sample size covers the native factorization threshold for
all factors up to the square-root Vaughan cutoff. -/
theorem eventually_typeI_dilation_input_scale (C : ℕ) (hC : 1 ≤ C) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℝ, 2 ≤ p → p ^ C ≤ Real.sqrt (Real.log (X : ℝ)) →
      Real.exp ((21 * p + C) ^ C) ≤ Real.exp (-21 * p) * ((X : ℝ) / X.sqrt) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_power_budget_le_log_quarter C hC (a := 21) (b := 21) (by norm_num) (by norm_num)]
    with X hX hbudget
  intro p hp hpX
  have hx : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hsqrt : (X.sqrt : ℝ) ≤ Real.sqrt (X : ℝ) :=
    (Real.le_sqrt (Nat.cast_nonneg _) hx.le).mpr (by exact_mod_cast Nat.sqrt_le' X)
  have hD : (0 : ℝ) < X.sqrt := Nat.cast_pos.mpr (Nat.sqrt_pos.mpr hX)
  have h := hbudget p hp hpX
  have hscale : Real.exp ((21 * p + (C : ℝ)) ^ C + 21 * p) ≤ (X : ℝ) / X.sqrt := calc
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (X : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    _ = Real.sqrt (X : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, mul_comm]
    _ ≤ _ := (le_div_iff₀ hD).mpr (by
      calc
        _ ≤ Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt hx.le)
  calc
    _ = Real.exp (-21 * p) * Real.exp ((21 * p + C) ^ C + 21 * p) := by
      rw [← Real.exp_add, show -21 * p + ((21 * p + (C : ℝ)) ^ C + 21 * p) =
        (21 * p + C) ^ C by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le

/-- The arithmetic alternative at fixed fourth-root cutoffs applies to the
original evaluations of the progression test and bounds its modulus. -/
theorem eventually_prime_cramer_fourth_root_correlation_cases :
    ∀ᶠ X : ℕ in atTop, ∀ {a b q r : ℕ}, a ≤ b → b ≤ X → r < q →
      ∀ (F : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → ∀ p : ℝ,
        max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
        p ≤ Real.log (X : ℝ) ^ (1 / 20 : ℝ) →
        Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X)
          (fun n => if n ∈ residueSlice ((a : ℤ) + 1) ((b - a : ℕ) : ℤ) (r : ZMod q)
            then F n else 0) →
        let A := (Finset.Ioc a b).filter (fun n => n % q = r)
        let G : ℕ → ℂ := fun n => F n
        (q : ℝ) < Real.exp (11 * p) ∧
          (DenseTypeIPrefixes X X.sqrt A G (Real.exp (-20 * p)) ∨
            ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
              (X : ℝ) * Real.exp (-20 * p) <
                ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A G‖) := by
  filter_upwards [eventually_progression_modulus_lt_exp_of_large_prime_correlation,
    eventually_prime_cramer_large_residue_correlation_cases] with X hmodulus hcases
  intro a b q r hab hbX hr F hF p hp hpX hlarge A G
  let P := residueSlice ((a : ℤ) + 1) ((b - a : ℕ) : ℤ) (r : ZMod q)
  let J : ℤ → ℂ := fun n => if n ∈ P then F n else 0
  have hq : 0 < q := (Nat.zero_le _).trans_lt hr
  have hJ (n : ℤ) (_ : n ∈ interval 1 (X : ℤ)) : ‖J n‖ ≤ 1 := by
    dsimp only [J]
    split
    · exact hF n
    · simp
  have hsupport (n : ℤ) (_ : n ∈ interval 1 (X : ℤ)) (hn : (n : ZMod q) ≠ (r : ZMod q)) :
      J n = 0 := by
    have hnP : n ∉ P := fun h => hn (Finset.mem_filter.mp h).2
    simp [J, hnP]
  refine ⟨hmodulus hq (r : ZMod q) J hJ hsupport p hp hpX hlarge, ?_⟩
  have hstar : (fun n => if n ∈ P then star (F n) else 0) = fun n => star (J n) := by
    funext n
    by_cases hn : n ∈ P <;> simp [J, hn]
  have hlarge' : Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X)
      (fun n => if n ∈ P then star (F n) else 0) := by
    rw [hstar, intervalCorrelation_star]
    exact hlarge
  have h := hcases X.sqrt.sqrt X.sqrt.sqrt X.sqrt (Nat.sqrt_le_self X.sqrt)
    (Nat.sqrt_le X.sqrt) le_rfl (Nat.sqrt_le_self X) (Nat.sqrt_le_self X.sqrt)
    a b q r hab hbX hr (fun n => star (F n)) (fun n => by simpa only [norm_star] using hF n)
    p hp hpX hlarge'
  simpa only [star_star] using h

end PrimeUniformity
