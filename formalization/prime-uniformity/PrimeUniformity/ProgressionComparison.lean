module

public import PrimeUniformity.CramerAPDecay
public import PrimeUniformity.CutoffDyadicScale
public import PrimeUniformity.PrimeProgressions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- The Cramér sieve has stretched-exponential discrepancy on reduced
progressions at the strict analytic cutoff. -/
theorem eventually_cramerAP_strictCutoff_error :
    ∀ᶠ X : ℕ in atTop,
      ∀ (q : ℕ), 0 < q → q ≤ strictPrimeUniformityCutoff X → ∀ (a : ZMod q), IsUnit a →
        ∀ (start len : ℤ), 0 ≤ len → len ≤ (X : ℤ) →
          |(∑ n ∈ residueSlice start len a, cramerWeight (strictPrimeUniformityCutoff X) n) -
            (len : ℝ) / (q.totient : ℝ)| ≤
            4 * (X : ℝ) * Real.exp (-(Real.log (X : ℝ) ^ (1 / 10 : ℝ))) := by
  filter_upwards [eventually_cramerCutoff_dyadic_scale] with X hX
  obtain ⟨hQ, hk, hk', hN, hNk, _⟩ := hX
  intro q hq hqQ a ha start len hlen hlenX
  have hlen' : len ≤ (2 : ℤ) ^ cramerIntervalDyadicIndex X :=
    hlenX.trans (by exact_mod_cast hk)
  refine (cramerAP_error_le_dyadic hq hqQ
    ((strictPrimeUniformityCutoff_le X).trans hQ) hN hNk start len hlen hlen' a ha).trans ?_
  have hkR : (2 : ℝ) ^ cramerIntervalDyadicIndex X ≤ 2 * (X : ℝ) := by exact_mod_cast hk'
  calc
    _ ≤ (2 * (2 * (X : ℝ))) * Real.exp (-(Real.log (X : ℝ) ^ (1 / 10 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hkR (by norm_num))
        (half_pow_cramerCutoffDyadicIndex_le X) (by positivity) (by positivity)
    _ = _ := by ring

/-- A large-modulus prime theorem and the finite Cramér sieve give the required
comparison on reduced progressions of modulus below the analytic cutoff. -/
theorem uniform_prime_cramer_reduced_progressions (h : UniformPrimePrefixEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ U V : ℕ, U ≤ V → V ≤ X →
        ∀ (q : ℕ), 0 < q → q ≤ strictPrimeUniformityCutoff X → ∀ (a : ZMod q), IsUnit a →
          |∑ n ∈ residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a,
            (vonMangoldtWeight n - cramerWeight (strictPrimeUniformityCutoff X) n)| ≤
            C * (X : ℝ) * Real.exp (-c * Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
  obtain ⟨cp, Cp, hcp, hCp, hprime⟩ := uniform_prime_interval_of_large_modulus h
  let c := min cp 1
  refine ⟨c, Cp + 4, lt_min hcp one_pos, by positivity, ?_⟩
  filter_upwards [hprime, eventually_cramerAP_strictCutoff_error,
    eventually_ge_atTop (1 : ℕ)] with X hprime hcramer hX
  intro U V hUV hV q hq hqQ a ha
  have hqR : (q : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
    have hq' : q ≤ primeUniformityCutoff X := hqQ.trans (strictPrimeUniformityCutoff_le X)
    exact (show (q : ℝ) ≤ (primeUniformityCutoff X : ℝ) by exact_mod_cast hq').trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hlen : ((V - U : ℕ) : ℤ) ≤ (X : ℤ) := by
    exact_mod_cast (Nat.sub_le V U).trans hV
  have hp := hprime U V hUV hV q hq a ha hqR
  have hm := hcramer q hq hqQ a ha ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) (by positivity) hlen
  let M := ((V - U : ℕ) : ℝ) / (q.totient : ℝ)
  let S := residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a
  let F := ∑ n ∈ S, vonMangoldtWeight n
  let G := ∑ n ∈ S, cramerWeight (strictPrimeUniformityCutoff X) n
  let R := Real.log (X : ℝ) ^ (1 / 10 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hX)) _
  have hpc : -cp * R ≤ -c * R := mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hR
  have hmc : -R ≤ -c * R := by
    simpa only [neg_one_mul] using
      mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right cp (1 : ℝ))) hR
  rw [Finset.sum_sub_distrib]
  change |F - G| ≤ _
  rw [show F - G = (F - M) - (G - M) by ring]
  refine (abs_sub _ _).trans ?_
  calc
    _ ≤ Cp * (X : ℝ) * Real.exp (-cp * R) + 4 * (X : ℝ) * Real.exp (-R) :=
      add_le_add hp (by simpa only [G, M, S, R, Int.cast_natCast] using hm)
    _ ≤ Cp * (X : ℝ) * Real.exp (-c * R) + 4 * (X : ℝ) * Real.exp (-c * R) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpc) (by positivity))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmc) (by positivity))
    _ = _ := by ring

end PrimeUniformity
