module

public import PrimeUniformity.CramerBoundary
public import PrimeUniformity.CramerCutoff
public import PrimeUniformity.PrimePowers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter

private theorem cramerWeight_previous_eq_of_not_prime {p : ℕ} (hp : ¬p.Prime) (n : ℤ) :
    cramerWeight (p - 1) n = cramerWeight p n := by
  have hs : cramerPrimeSet (p - 1) = cramerPrimeSet p := by
    ext q
    simp only [cramerPrimeSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hle, hq⟩
      exact ⟨hle.trans (Nat.sub_le _ _), hq⟩
    · rintro ⟨hle, hq⟩
      have hne : q ≠ p := fun he => hp (he ▸ hq)
      exact ⟨by omega, hq⟩
  classical
  simp only [cramerWeight, cramerNormalization, hs]

private theorem intervalCubeSum_zero (d X : ℕ) : intervalCubeSum d X (fun _ => 0) = 0 := by
  simp [intervalCubeSum, cubeProduct_eq_zero_of_vertex d (intervalWeight X (fun _ => 0))
    _ _ (fun _ => false) (by simp [intervalWeight])]

/-- The strict prime cutoff from Leng and the closed cutoff used in the
application differ by a weight with arbitrary logarithmic moment savings. -/
theorem strictCutoffError_intervalMomentBound (d A : ℕ) :
    IntervalMomentBound d.succ A (fun X n =>
      cramerWeight (strictPrimeUniformityCutoff X) n - cramerWeight (primeUniformityCutoff X) n) := by
  obtain ⟨C, hC, hfinite⟩ := exists_intervalCubeSum_cramerBoundary_le d
  obtain ⟨B, hB, hnorm⟩ := eventually_abs_cramerWeight_le_log_pow
  let m : ℕ := 2 ^ d.succ
  let K : ℝ := (2 * ((d.succ : ℝ) + 1)) ^ (d.succ + 1)
  let D : ℝ := C * (2 + (2 : ℝ) ^ m) * B ^ m
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * K, by dsimp [K]; positivity, ?_⟩
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnorm, eventually_ge_atTop (2 * (d.succ + 1)), ht.eventually_ge_atTop 1,
    eventually_log_pow_le_exp_log_rpow (8 * m + A) (c := 1 / 10) (by norm_num)] with X hB_X hX hL hrate
  let L := Real.log (X : ℝ)
  let p := primeUniformityCutoff X
  let x : ℝ := X
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 ≤ (D * K / L ^ A) * intervalCubeSum d.succ X (fun _ => 1) := by
    rw [intervalCubeSum_one_eq_card]
    dsimp [K]
    positivity
  rcases strictPrimeUniformityCutoff_cases X with hsame | ⟨hprev, hpExp⟩
  · simpa only [hsame, sub_self, intervalCubeSum_zero] using hz
  by_cases hp : p.Prime
  · have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp₀ : 0 < (p : ℝ) := by linarith
    have hm : 1 ≤ m := Nat.one_le_pow _ _ (by decide)
    let b := B * L ^ (8 : ℕ)
    let w (n : ℤ) := cramerWeight (p - 1) n - cramerWeight p n
    have hb : 0 ≤ b := by positivity
    have hraw := (le_abs_self (intervalCubeSum d.succ X w)).trans
      (hfinite X p hp b hb (fun n _ _ => hB_X _ (Nat.sub_le _ _) n))
    have hpow : (b / ((p : ℝ) - 1)) ^ m ≤ 2 * b ^ m / (p : ℝ) := by
      have hp₁ : 1 ≤ (p : ℝ) - 1 := by linarith
      have hhalf : (p : ℝ) / 2 ≤ ((p : ℝ) - 1) ^ m := by
        calc
          _ ≤ (p : ℝ) - 1 := by linarith
          _ ≤ _ := by simpa only [pow_one] using pow_le_pow_right₀ hp₁ hm
      rw [div_pow]
      calc
        _ ≤ b ^ m / ((p : ℝ) / 2) :=
          div_le_div_of_nonneg_left (pow_nonneg hb _) (by positivity) hhalf
        _ = _ := by field_simp [hp₀.ne']
    have hdvd : (↑(X / p : ℕ) : ℝ) ≤ x / (p : ℝ) := by
      apply (le_div_iff₀ hp₀).mpr
      dsimp [x]
      exact_mod_cast Nat.div_mul_le_self X p
    have hupper : intervalCubeSum d.succ X w ≤
        D * x ^ (d.succ + 1) * L ^ (8 * m) / (p : ℝ) := by
      refine hraw.trans ?_
      calc
        _ ≤ C * (x ^ (d.succ + 1) * (2 * b ^ m / (p : ℝ)) +
            (x / (p : ℝ)) * x ^ d.succ * (2 * b) ^ m) := by
          gcongr
        _ = _ := by
          dsimp only [D]
          rw [mul_pow (2 : ℝ), show b ^ m = B ^ m * L ^ (8 * m) by dsimp [b]; rw [mul_pow, pow_mul]]
          rw [pow_succ x (d.succ)]
          simp only [div_eq_mul_inv]
          ring
    rw [hprev]
    change intervalCubeSum d.succ X w ≤ (D * K / L ^ A) * intervalCubeSum d.succ X (fun _ => 1)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hLpos _)).mpr
    calc
      _ ≤ (D * x ^ (d.succ + 1) * L ^ (8 * m) / (p : ℝ)) * L ^ A :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = (D * x ^ (d.succ + 1)) * (L ^ (8 * m + A) / (p : ℝ)) := by
        rw [pow_add]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (D * x ^ (d.succ + 1)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_one hp₀).mpr
        exact hrate.trans_eq hpExp.symm
      _ = D * x ^ (d.succ + 1) := mul_one _
      _ ≤ D * (K * intervalCubeSum d.succ X (fun _ => 1)) :=
        mul_le_mul_of_nonneg_left (intervalCubeSum_one_ge hX) hD.le
      _ = _ := (mul_assoc _ _ _).symm
  · have hn : ¬(primeUniformityCutoff X).Prime := hp
    simpa only [hprev, cramerWeight_previous_eq_of_not_prime hn, sub_self, intervalCubeSum_zero] using hz

/-- The ordinary von Mangoldt estimate with the strict cutoff suffices
for the cyclic uniformity estimate with the closed cutoff. -/
theorem gowersUniformityEstimate_of_vonMangoldt_strict_cramer (d A : ℕ)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hprime : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d.succ X
        (fun n => vonMangoldtWeight n - cramerWeight (strictPrimeUniformityCutoff X) n) ≤
          (C * Real.exp (-(Real.log (X : ℝ) ^ c))) * intervalCubeSum d.succ X (fun _ => 1)) :
    GowersUniformityEstimate d.succ A := by
  apply gowersUniformityEstimate_of_interval
  have hprime' := intervalMomentBound_primeWeight_of_vonMangoldt
    (IntervalMomentBound.of_stretched_exponential hC hc hprime A)
  have h := hprime'.add (strictCutoffError_intervalMomentBound d A)
  have hsum : (fun X n => (primeWeight n - cramerWeight (strictPrimeUniformityCutoff X) n) +
      (cramerWeight (strictPrimeUniformityCutoff X) n - cramerWeight (primeUniformityCutoff X) n)) =
      fun X n => primeWeight n - cramerWeight (primeUniformityCutoff X) n := by
    funext X n
    ring
  rwa [hsum] at h

end PrimeUniformity
