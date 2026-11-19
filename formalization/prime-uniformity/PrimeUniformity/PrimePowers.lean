module

public import PrimeUniformity.IntervalSupport
public import PrimeUniformity.SiegelModel
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter

/-- The ordinary von Mangoldt weight, including the proper prime powers. -/
noncomputable def vonMangoldtWeight (n : ℤ) : ℝ :=
  ArithmeticFunction.vonMangoldt n.toNat

private noncomputable def properPowerBases (X : ℕ) : Finset (Fin X) := by
  classical
  exact Finset.univ.filter (fun i => IsPrimePow (i.val + 1) ∧ ¬(i.val + 1).Prime)

private theorem card_properPowerBases_le (X : ℕ) :
    (properPowerBases X).card ≤ (X.sqrt + 1) * (Nat.log 2 X + 1) := by
  classical
  let pairs := (Finset.range (X.sqrt + 1)) ×ˢ (Finset.range (Nat.log 2 X + 1))
  let image := pairs.image (fun a => a.1 ^ a.2)
  have himage : (properPowerBases X).card ≤ image.card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin X => i.val + 1) _ _
    · intro i hi
      have hi' : IsPrimePow (i.val + 1) ∧ ¬(i.val + 1).Prime := by
        simpa [properPowerBases] using hi
      have hiX : i.val + 1 ≤ X := i.isLt
      obtain ⟨k, hk, hk₀, p, _, heq, hp⟩ := (isPrimePow_nat_iff_bounded_log _).mp hi'.1
      have hk₂ : 2 ≤ k := by
        by_contra! hn
        have hk₁ : k = 1 := by omega
        exact hi'.2 (by simpa [heq, hk₁] using hp)
      have hpX : p ≤ X.sqrt := by
        apply Nat.le_sqrt'.mpr
        exact (Nat.pow_le_pow_right hp.pos hk₂).trans (heq ▸ hiX)
      rw [show image = pairs.image (fun a => a.1 ^ a.2) from rfl]
      apply Finset.mem_image.mpr
      exact ⟨(p, k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpX),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans (Nat.log_mono_right hiX)))⟩, heq.symm⟩
    · intro a _ b _ hab
      change a.val + 1 = b.val + 1 at hab
      apply Fin.ext
      omega
  refine himage.trans ((Finset.card_image_le (s := pairs)).trans ?_)
  simp [pairs]

private theorem vonMangoldtWeight_eq_primeWeight_of_prime {n : ℤ} (hn : 0 ≤ n)
    (hp : n.toNat.Prime) : vonMangoldtWeight n = primeWeight n := by
  rw [vonMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_prime hp, primeWeight, if_pos hp]
  rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg hn]

private theorem norm_intervalWeight_primePowerError_le {X : ℕ} (hX : 1 ≤ X) (n : ℤ) :
    ‖intervalWeight X (fun n => primeWeight n - vonMangoldtWeight n) n‖ ≤ Real.log (X : ℝ) := by
  simp only [intervalWeight]
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  split
  · rename_i hn
    by_cases hp : n.toNat.Prime
    · simp [vonMangoldtWeight_eq_primeWeight_of_prime (by omega : 0 ≤ n) hp, hlog]
    · simp only [primeWeight, if_neg hp, zero_sub, Complex.norm_real, norm_neg, vonMangoldtWeight]
      rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
      apply Real.log_le_log
      · exact_mod_cast (show 0 < n.toNat by omega)
      · exact_mod_cast (show n.toNat ≤ X by omega)
  · simpa using hlog

private theorem intervalWeight_primePowerError_eq_zero {X : ℕ} (i : Fin X)
    (hi : i ∉ properPowerBases X) :
    intervalWeight X (fun n => primeWeight n - vonMangoldtWeight n) (intervalEndpoint i) = 0 := by
  classical
  have htoNat : (intervalEndpoint i).toNat = i.val + 1 := by
    rw [show intervalEndpoint i = ((i.val + 1 : ℕ) : ℤ) by simp [intervalEndpoint]]
    simp
  by_cases hp : (i.val + 1).Prime
  · rw [intervalWeight]
    have hn : 0 ≤ intervalEndpoint i := by unfold intervalEndpoint; positivity
    have heq := vonMangoldtWeight_eq_primeWeight_of_prime hn (by rwa [htoNat])
    simp [heq]
  · have hpow : ¬IsPrimePow (i.val + 1) := by simpa [properPowerBases, hp] using hi
    simp [intervalWeight, primeWeight, vonMangoldtWeight, htoNat, hp,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]

/-- The contribution of the proper prime powers to the unnormalized moment. -/
theorem intervalCubeSum_primePowerError_le (d X : ℕ) (hX : 1 ≤ X) :
    intervalCubeSum d X (fun n => primeWeight n - vonMangoldtWeight n) ≤
      ((X.sqrt + 1 : ℕ) : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) *
        (X : ℝ) ^ d * Real.log (X : ℝ) ^ (2 ^ d : ℕ) := by
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hX)
  refine (intervalCubeSum_le_support d X _ (properPowerBases X) hL
    (norm_intervalWeight_primePowerError_le hX) (intervalWeight_primePowerError_eq_zero)).trans ?_
  have hcard : ((properPowerBases X).card : ℝ) ≤
      ((X.sqrt + 1 : ℕ) : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) := by
    exact_mod_cast card_properPowerBases_le X
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) (pow_nonneg hL _)

private theorem sqrt_cast_le (X : ℕ) : (X.sqrt : ℝ) ≤ Real.sqrt X := by
  have hsq : (X.sqrt : ℝ) ^ 2 ≤ (X : ℝ) := by
    exact_mod_cast (Nat.le_sqrt'.mp (show X.sqrt ≤ X.sqrt by rfl))
  have hx : 0 ≤ (X : ℝ) := by positivity
  have hs := Real.sq_sqrt hx
  by_contra! h
  exact (not_lt_of_ge (hsq.trans_eq hs.symm))
    (pow_lt_pow_left₀ h (Real.sqrt_nonneg _) (by decide))

/-- The binary logarithm on natural numbers is bounded by the real change-of-base formula. -/
theorem log_nat_cast_le_log_div_log_two {X : ℕ} (hX : 1 ≤ X) :
    (Nat.log 2 X : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
  have hpow : (2 : ℝ) ^ Nat.log 2 X ≤ (X : ℝ) :=
    by exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog

/-- Removing the proper prime powers preserves arbitrary logarithmic savings. -/
theorem primePowerError_intervalMomentBound (d A : ℕ) :
    IntervalMomentBound d A (fun _ n => primeWeight n - vonMangoldtWeight n) := by
  let K : ℝ := (2 * ((d : ℝ) + 1)) ^ (d + 1)
  let D : ℝ := 2 * (1 / Real.log 2 + 1)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * K, by dsimp [K]; positivity, ?_⟩
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hex := ht.eventually
    ((isLittleO_pow_exp_pos_mul_atTop (A + (2 ^ d : ℕ) + 1) (show 0 < (1 / 2 : ℝ) by norm_num)).bound
      one_pos)
  filter_upwards [eventually_ge_atTop (2 * (d + 1)), ht.eventually_ge_atTop 1, hex] with X hX hlog hex
  let x : ℝ := X
  let L := Real.log x
  let m : ℕ := 2 ^ d
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hX₁ : 1 ≤ X := by omega
  have hx₁ : 1 ≤ x := by dsimp [x]; exact_mod_cast hX₁
  have hx : 0 < x := zero_lt_one.trans_le hx₁
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hsqrt : ((X.sqrt + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    push_cast
    have hr₁ : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx₁
    linarith [sqrt_cast_le X]
  have hlogX : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ (1 / Real.log 2 + 1) * L := by
    push_cast
    calc
      _ ≤ L / Real.log 2 + L := add_le_add (log_nat_cast_le_log_div_log_two hX₁) hlog
      _ = _ := by simp only [div_eq_mul_inv]; ring
  have hdecay : L ^ (A + m + 1) ≤ Real.sqrt x := by
    change ‖L ^ (A + m + 1)‖ ≤ 1 * ‖Real.exp ((1 / 2 : ℝ) * L)‖ at hex
    have he : Real.exp ((1 / 2 : ℝ) * L) = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, mul_comm]
    simpa only [one_mul, Real.norm_of_nonneg (pow_nonneg hL.le _),
      he, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hex
  have hpre := intervalCubeSum_primePowerError_le d X hX₁
  have hraw : intervalCubeSum d X (fun n => primeWeight n - vonMangoldtWeight n) ≤
      D * (Real.sqrt x * L ^ (m + 1)) * x ^ d := by
    refine hpre.trans ?_
    calc
      _ ≤ ((2 * Real.sqrt x) * ((1 / Real.log 2 + 1) * L)) * x ^ d * L ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hsqrt hlogX (by positivity) (by positivity)) (by positivity)) (by positivity)
      _ = _ := by dsimp [D]; rw [pow_succ]; ring
  have hgain : (Real.sqrt x * L ^ (m + 1)) * L ^ A ≤ x := by
    calc
      _ = Real.sqrt x * L ^ (A + m + 1) := by
        rw [mul_assoc, ← pow_add, show m + 1 + A = A + m + 1 by omega]
      _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hdecay (Real.sqrt_nonneg _)
      _ = x := by rwa [← pow_two]
  change intervalCubeSum d X (fun n => primeWeight n - vonMangoldtWeight n) ≤
    (D * K / L ^ A) * intervalCubeSum d X (fun _ => 1)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hL _)).mpr
  calc
    _ ≤ (D * (Real.sqrt x * L ^ (m + 1)) * x ^ d) * L ^ A :=
      mul_le_mul_of_nonneg_right hraw (by positivity)
    _ = (D * x ^ d) * ((Real.sqrt x * L ^ (m + 1)) * L ^ A) := by ring
    _ ≤ (D * x ^ d) * x := mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = D * x ^ (d + 1) := by rw [pow_succ]; ring
    _ ≤ D * (K * intervalCubeSum d X (fun _ => 1)) :=
      mul_le_mul_of_nonneg_left (intervalCubeSum_one_ge hX) hD.le
    _ = _ := (mul_assoc _ _ _).symm

/-- An interval estimate for the ordinary von Mangoldt weight also holds when
the weight is restricted to primes. -/
theorem intervalMomentBound_primeWeight_of_vonMangoldt {d A : ℕ} {w : ℕ → ℤ → ℝ}
    (h : IntervalMomentBound d.succ A (fun X n => vonMangoldtWeight n - w X n)) :
    IntervalMomentBound d.succ A (fun X n => primeWeight n - w X n) := by
  have hsum : (fun X n => (primeWeight n - vonMangoldtWeight n) +
      (vonMangoldtWeight n - w X n)) = fun X n => primeWeight n - w X n := by
    funext X n
    ring
  have hadd := (primePowerError_intervalMomentBound d.succ A).add h
  rwa [hsum] at hadd

/-- The prime-to-Siegel estimate can be supplied with the ordinary von Mangoldt
weight, as in the stretched-exponential estimate of Leng. -/
theorem gowersUniformityEstimate_of_vonMangoldt_siegel (d A : ℕ)
    (exception : ℕ → Option SiegelCorrection) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hprime : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d.succ X (fun n => vonMangoldtWeight n - siegelWeight X (exception X) n) ≤
        (C * Real.exp (-(Real.log (X : ℝ) ^ c))) * intervalCubeSum d.succ X (fun _ => 1))
    (hcorrection : IntervalMomentBound d.succ A
      (fun X n => siegelWeight X (exception X) n - cramerWeight (primeUniformityCutoff X) n)) :
    GowersUniformityEstimate d.succ A := by
  exact gowersUniformityEstimate_of_model_comparisons d A (fun X => siegelWeight X (exception X))
    (intervalMomentBound_primeWeight_of_vonMangoldt
      (IntervalMomentBound.of_stretched_exponential hC hc hprime A)) hcorrection

/-- When the cutoff excludes exceptional zeros, an ordinary von Mangoldt
estimate against Cramér's model supplies the prime uniformity estimate directly. -/
theorem gowersUniformityEstimate_of_vonMangoldt_cramer (d A : ℕ)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hprime : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d.succ X
        (fun n => vonMangoldtWeight n - cramerWeight (primeUniformityCutoff X) n) ≤
          (C * Real.exp (-(Real.log (X : ℝ) ^ c))) * intervalCubeSum d.succ X (fun _ => 1)) :
    GowersUniformityEstimate d.succ A := by
  apply gowersUniformityEstimate_of_interval
  exact intervalMomentBound_primeWeight_of_vonMangoldt
    (IntervalMomentBound.of_stretched_exponential hC hc hprime A)

end PrimeUniformity
