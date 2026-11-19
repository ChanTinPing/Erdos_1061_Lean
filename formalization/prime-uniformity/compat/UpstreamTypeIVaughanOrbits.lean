import UpstreamTypeIBranchFinish
import PrimeUniformity.TypeIVaughanScale
import PrimeUniformity.UpstreamTypeICommonNear
import PrimeUniformity.UpstreamTypeIEventualOrbitRecovery

namespace PrimeUniformity

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- Budget containing the fast basis heights, common rational denominator,
and smooth factors output by ambient Type I recovery. -/
def typeIVaughanFactorBudget (s C : ℕ) (p P : ℝ) : ℝ :=
  let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
  let u := (C : ℝ) * typeIVaughanLogBudget s p P ^ 2
  Z + u + s * (u + 2) ^ 36

private theorem typeI_smooth_bound_exponent {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (u + 2) ^ (18 : ℕ) + u ≤ (v + 2) ^ (19 : ℕ) := by
  have hbase : 1 ≤ u + 2 := by linarith
  have hone : 1 ≤ (u + 2) ^ (18 : ℕ) := one_le_pow₀ hbase
  have hprod : u + 1 ≤ (u + 2) ^ (18 : ℕ) * (u + 1) :=
    le_mul_of_one_le_left (by positivity) hone
  have hfactor (a : ℝ) : a + a * (u + 1) = a * (u + 2) := by ring
  calc
    _ ≤ (u + 2) ^ (18 : ℕ) + (u + 2) ^ (18 : ℕ) * (u + 1) :=
      add_le_add le_rfl ((le_add_of_nonneg_right (by norm_num)).trans hprod)
    _ = (u + 2) ^ (18 : ℕ) * (u + 2) := hfactor _
    _ = (u + 2) ^ (19 : ℕ) := (pow_succ (u + 2) 18).symm
    _ ≤ _ := pow_le_pow_left₀ (zero_le_one.trans hbase) (add_le_add huv le_rfl) _

private theorem typeI_rows_card_bound {s n : ℕ} (m : Fin s → ℕ) (hm : ∀ j, m j ≤ n) :
    (Fintype.card ((Σ j : Fin s, Fin (m j)) × Bool) : ℝ) ≤ 2 * s * n := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hsum : ∑ j, m j ≤ s * n := by
    calc
      _ ≤ ∑ _j : Fin s, n := Finset.sum_le_sum fun j _ => hm j
      _ = _ := by simp
  calc
    _ ≤ ((s * n * 2 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.mul_le_mul_right _ hsum)
    _ = _ := by push_cast; ring

/-- Recover exact, normalized Type I factors from the ambient rows of the
retained Vaughan band, with a polynomial complexity budget. -/
theorem exists_typeI_orbit_factors_of_common_near (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {r X : ℕ} {p P : ℝ} (Z : NativeRankedPrimeTest s (r + 1) X p)
        (ω : Fin Z.test.dim → ℕ)
        (_hF : ∀ d, Z.test.model.filtration.layer d =
          Submodule.span ℚ (Z.test.model.basis '' {i | d ≤ ω i}))
        (_hNorm : Z.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0
          Z.test.test.orbit = 1)
        (η : Z.test.L →ₗ[ℚ] ℚ)
        (W : LieSubalgebra ℚ Z.test.model.filtration.AssociatedGraded),
      (∀ x ∈ Z.test.model.filtration.gradedRefiltrationLayer W s, η x = 0) →
      0 ≤ p → 0 ≤ P → (Z.test.dim : ℝ) ≤ P → 0 < X →
      ∀ {i : ℕ}, i ≤ Nat.log 2 X.sqrt → ∀ (l : ℕ), (l : ℝ) ≤ Real.exp P →
      let t := typeIVaughanLogBudget s p P
      Real.exp (2 * ((C : ℝ) * t + 1)) ≤ (X : ℝ) →
      Real.exp (separationBudget ((C : ℝ) * t ^ 2)) ≤ (X : ℝ) →
      let L := 2 ^ (i + 1) - 1
      ∀ S : Finset ℕ, S ⊆ dyadicDilationInterval L →
      Real.exp (-((P + 2) ^ 5 + P + 21 * p)) * ((dyadicDilationInterval L).card : ℝ) ≤ S.card →
      NativeTypeICommonNear Z.test.model Z.rank W Z.test.test.orbit p P (X : ℝ) L l S →
      NativeTypeIOrbitFactors Z η (typeIVaughanFactorBudget s C p P) := by
  obtain ⟨C, hC, hRecover⟩ := exists_uniform_native_typeI_orbits_of_dense_rows s hs
  refine ⟨C, hC, ?_⟩
  intro r X p P Z ω hF hNorm η W hTop hp hP hn hX i hi l hl t hBig hSep L S hS hDensity hNear
  let D := Z.test.model
  let u := (C : ℝ) * t ^ 2
  let z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
  let b := ⌈Real.exp ((2 * P + z + 1 + 2) ^ 7)⌉₊
  let N := Z.test.dim * (s + 1) * 2 ^ s
  let A := b ^ N
  let H := (l : ℝ) * N * A * Real.exp P
  change NativeTypeICommonNear D Z.rank W Z.test.test.orbit p P (X : ℝ) L l S at hNear
  unfold NativeTypeICommonNear at hNear
  obtain ⟨hFast, hb, m, hm, φ, hker, hheight, c, hc, hnear⟩ := hNear
  obtain ⟨ht, hnt, hcard, hbt, hct, hHt, hdensity⟩ := typeI_vaughan_log_budget (l := l) (s := s) hp hP hn hl
  have hL : 0 < L := by
    change 0 < 2 ^ (i + 1) - 1
    rw [pow_succ]
    have hpow : 0 < (2 : ℕ) ^ i := by positivity
    omega
  have hside : Real.exp ((C : ℝ) * t) ≤ (X : ℝ) / L := typeI_vaughan_cofactor_exp_lower hX hi _ hBig
  have hDensity' : Real.exp (-t) * ((dyadicDilationInterval L).card : ℝ) ≤ S.card :=
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg _)).trans hDensity
  have hWindow : (X : ℝ) * Real.exp (-t) ≤ (X : ℝ) := by
    have hdecay : Real.exp (-t) ≤ 1 := (Real.exp_le_exp.mpr (neg_nonpos.mpr (zero_le_one.trans ht))).trans_eq Real.exp_zero
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hdecay
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨M, hM, hMBound, ε, K, U, γ, _, hK₀, hU₀, _, hε, hγ, hprod, hcoeff⟩ :=
    hRecover D Z.rank W ω hF Z.test.test.orbit hNorm φ hker b hb hheight c (fun j i => (hc j i).1) L
      ht hH hHt (fun j i => (Nat.cast_le.mpr (hc j i).2).trans hct) hnt hbt
      ((typeI_rows_card_bound m hm).trans hcard) hL hside (Nat.cast_pos.mpr hX) hWindow hSep S hS hDensity' hnear
  let v := typeIVaughanFactorBudget s C p P
  have hv : v = z + u + (s : ℝ) * (u + 2) ^ 36 := rfl
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hLast : 0 ≤ (s : ℝ) * (u + 2) ^ 36 := by positivity
  have hzv : z ≤ v := by
    rw [hv]
    exact (le_add_of_nonneg_right hu).trans (le_add_of_nonneg_right hLast)
  have huv : u ≤ v := by
    rw [hv]
    exact (le_add_of_nonneg_left hz).trans (le_add_of_nonneg_right hLast)
  have hMv : (s : ℝ) * (u + 2) ^ 36 ≤ v := by
    rw [hv]
    exact le_add_of_nonneg_left (add_nonneg hz hu)
  have hεv := CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr hX) hε
    (Real.exp_le_exp.mpr (typeI_smooth_bound_exponent hu huv))
  refine ⟨W, hTop, ?_, M, hM, hMBound.trans (Real.exp_le_exp.mpr hMv), ε, K, U, γ,
    hK₀, hU₀, hεv, hγ, hprod, hcoeff⟩
  intro j
  obtain ⟨e, he⟩ := hFast j
  exact ⟨e, fun a k => (he a k).trans hzv⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeI_orbit_factors_of_common_near
