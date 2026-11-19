import UpstreamTypeISamples
import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
import PrimeUniformity.UpstreamTypeIVaughanOrbits
import PrimeUniformity.UpstreamTypeIFromVaughanSamples

namespace PrimeUniformity

open Filter OAI.Erdos3
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

private theorem typeI_vaughan_cost_bounds {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcost : a + b + c + Real.log 4 ≤ L / 4) : a ≤ L / 2 ∧ b ≤ L ∧ c ≤ L := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [ha, hb, hc, hcost, hlog]

private theorem typeI_sampler_input_of_log_bound {X : ℕ} (hX : 0 < X) (p y : ℝ)
    (h : y + 21 * p ≤ Real.log (X : ℝ) / 2) :
    Real.exp y ≤ Real.exp (-21 * p) * ((X : ℝ) / X.sqrt) := by
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hD : 0 < (X.sqrt : ℝ) := Nat.cast_pos.mpr (Nat.sqrt_pos.mpr hX)
  have hNatSqrt : (X.sqrt : ℝ) ≤ Real.sqrt (X : ℝ) :=
    (Real.le_sqrt (Nat.cast_nonneg _) hX'.le).mpr (by exact_mod_cast Nat.sqrt_le' X)
  have hScale : Real.exp (y + 21 * p) ≤ (X : ℝ) / X.sqrt := calc
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (X : ℝ)) := Real.exp_le_exp.mpr (h.trans_eq (by ring))
    _ = Real.sqrt (X : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX', mul_comm]
    _ ≤ _ := (le_div_iff₀ hD).mpr ((mul_le_mul_of_nonneg_left hNatSqrt (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hX'.le))
  calc
    _ = Real.exp (-21 * p) * Real.exp (y + 21 * p) := by
      rw [← Real.exp_add, show -21 * p + (y + 21 * p) = y by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_left hScale (Real.exp_pos _).le

/-- The actual prepared Vaughan Type I case supplies the exact native
orbit factors with polynomial recovery and factor budgets. -/
theorem native_prime_prepared_typeI_factor_recovery (k : ℕ) : NativePrimePreparedTypeIFactorRecovery k := by
  let s := k + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  obtain ⟨C, hC, hSample⟩ := exists_native_typeI_common_dilation_family s hs
  obtain ⟨D, _, hOrbit⟩ := exists_typeI_orbit_factors_of_common_near s hs
  let Y : Polynomial ℕ := Polynomial.X
  let B := (21 * Y + Polynomial.C C) ^ C
  let P := B + Polynomial.C s * (21 * Y + 11 * Y)
  let Z := Y + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
  let N := P * Polynomial.C (s + 1) * Polynomial.C (2 ^ s)
  let T := 1 + ((P + 2) ^ 5 + P + 21 * Y) + ((2 * P + Z + 1 + 2) ^ 7 + 1) * (N + 1) +
    N + 2 * P + 2 * Polynomial.C s * P
  let U := Polynomial.C D * T ^ 2
  let P₀ := (B + 21 * Y) + 2 * (Polynomial.C D * T + 1) + ((U + 2) ^ 48 + (U + 2) ^ 24 + U + 1)
  let Q₀ := Z + U + Polynomial.C s * (U + 2) ^ 36
  refine ⟨P₀, Q₀, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  intro r _ p hp hcost W ω hω hnorm η hη hVert _ _ hq A F hlarge
  let P' := (21 * p + C) ^ C + (s : ℝ) * (21 * p + 11 * p)
  let t := typeIVaughanLogBudget s p P'
  let u := (D : ℝ) * t ^ 2
  let J := separationBudget u
  have hP₀ : P₀.eval₂ (Nat.castRingHom ℝ) p =
      ((21 * p + C) ^ C + 21 * p) + 2 * ((D : ℝ) * t + 1) + J := by
    simp [P₀, U, T, N, B, Z, P, Y, J, u, t, P', separationBudget, typeIVaughanLogBudget,
      Polynomial.eval₂_pow]
  have hQ₀ : Q₀.eval₂ (Nat.castRingHom ℝ) p = typeIVaughanFactorBudget s D p P' := by
    simp [Q₀, U, T, N, B, Z, P, Y, P', typeIVaughanFactorBudget, typeIVaughanLogBudget, Polynomial.eval₂_pow]
  rw [hP₀] at hcost
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith only [hp₂]
  have hpP : p ≤ P' := typeI_vaughan_sample_complexity_ge s C hC hp₂
  have hPpos : 0 ≤ P' := hp₀.trans hpP
  have ht : 0 ≤ t := by unfold t typeIVaughanLogBudget; positivity
  have hJ : 0 ≤ J := separationBudget_nonneg (by dsimp [u]; positivity)
  obtain ⟨hraw, hscale, hsep⟩ := typeI_vaughan_cost_bounds
    (show 0 ≤ (21 * p + C) ^ C + 21 * p by positivity)
    (show 0 ≤ 2 * ((D : ℝ) * t + 1) by positivity) hJ hcost
  have hlong := typeI_sampler_input_of_log_bound hX p ((21 * p + C) ^ C) hraw
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hBig := (Real.exp_le_exp.mpr hscale).trans_eq (Real.exp_log hX')
  have hSep := (Real.exp_le_exp.mpr hsep).trans_eq (Real.exp_log hX')
  obtain ⟨i, hi, V, l, v, S, hS, _, hDensity, hv, _, hHeight, hl, hlp, hTop, hFactors⟩ :=
    hSample W.test.model ω hω W.test.test η p hp₂ W.test.complexity W.test.bound hη hVert
      (a := W.test.U) (b := W.test.V) (q := W.test.q) (z := W.test.a.val)
      hX W.test.endpoints.2.1 W.test.endpoints.2.2 hq.le hlong hlarge
  let L := 2 ^ (i + 1) - 1
  obtain ⟨hL, _, hSide⟩ := typeI_dyadic_scale_bounds hX hi
  have hS' : S ⊆ dyadicDilationInterval L := by
    change S ⊆ dyadicDilationInterval (2 ^ (i + 1) - 1)
    rw [dyadicDilationInterval_pow_sub_one]
    exact fun _ hd => Finset.mem_Ico.mpr (mem_dyadicFactorBlock.mp (hS hd)).2.2
  have hDensity' : Real.exp (-((P' + 2) ^ 5 + P' + 21 * p)) * ((dyadicDilationInterval L).card : ℝ) ≤ S.card := by
    simpa only [L, card_dyadicDilationInterval_pow_sub_one, Nat.cast_pow, Nat.cast_ofNat] using hDensity
  have hn : (W.test.dim : ℝ) ≤ P' := W.test.complexity.1.1.trans hpP
  have hFastTop := W.test.model.filtration.frequency_zero_on_refiltered_top W.test.model.basis ω hω V η hTop
  have hNear := exists_native_typeI_near_of_common_factors W.test.model W.rank hs ω hω W.test.test
    V v hv hp₀ hPpos hn W.complexity hHeight L l hl (div_pos hX' (Nat.cast_pos.mpr hL)) hSide S hFactors
  rw [hQ₀]
  exact hOrbit W ω hω hnorm η V hFastTop hp₀ hPpos hn hX hi l hlp hBig hSep S hS' hDensity' hNear

/-- The prepared Type I branch produces an actual correlated test of
strictly smaller rank. -/
theorem native_prime_prepared_typeI_branch (k : ℕ) : NativePrimePreparedTypeIBranch k :=
  native_prime_prepared_typeI_branch_of_factors (native_prime_prepared_typeI_factor_recovery k)

end PrimeUniformity

#print axioms PrimeUniformity.native_prime_prepared_typeI_factor_recovery
#print axioms PrimeUniformity.native_prime_prepared_typeI_branch
