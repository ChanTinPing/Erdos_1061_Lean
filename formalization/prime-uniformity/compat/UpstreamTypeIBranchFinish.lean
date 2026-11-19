import UpstreamBranchBudget
import UpstreamPrimePreparedRankBranches
import UpstreamTypeIRankDrop

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- Normalized Type I factors at one complexity budget, together with
the bounded fast layers and vanishing top frequency. -/
def NativeTypeIOrbitFactors {s r X : ℕ} {p : ℝ}
    (Z : NativeRankedPrimeTest s (r + 1) X p) (η : Z.test.L →ₗ[ℚ] ℚ) (t : ℝ) : Prop :=
  let D := Z.test.model
  let w : Unit → ℕ := fun _ => 1
  ∃ W : LieSubalgebra ℚ D.filtration.AssociatedGraded,
    (∀ x ∈ D.filtration.gradedRefiltrationLayer W s, η x = 0) ∧
    (∀ j : Fin s, ∃ e : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (j.val + 1)),
        ∀ i k, rationalLogHeight (D.basis.repr (e i : Z.test.L) k) ≤ t) ∧
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp t ∧
      ∃ ε K U γ : D.filtration.realification.PolynomialOrbit w,
        D.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧
        D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
        CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
          (Real.exp ((t + 2) ^ (19 : ℕ))) ε.log ∧
        CoefficientGrid (D.basis.baseChange ℝ) M γ.log ∧ ε * K * U * γ = Z.test.test.orbit ∧
        ∀ j : Fin s,
          coefficients K.log (Finsupp.single () (j.val + 1)) ∈
            (Z.rank.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
          coefficients U.log (Finsupp.single () (j.val + 1)) ∈
            D.filtration.realGradedRefiltrationLayer W (j.val + 1)

/-- Recovering the exact Type I factors at polynomial complexity suffices
when their recovery scale fits into a quarter of the log length. -/
def NativePrimePreparedTypeIFactorRecovery (k : ℕ) : Prop :=
  ∃ P Q : Polynomial ℕ, ∀ᶠ X : ℕ in atTop,
    ∀ r < k + 1, ∀ p : ℝ,
      max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p + Real.log 4 ≤ Real.log (X : ℝ) / 4 →
      ∀ Z : NativeRankedPrimeTest (k + 1) (r + 1) X p,
      ∀ ω : Fin Z.test.dim → ℕ,
      (∀ j, Z.test.model.filtration.layer j =
        Submodule.span ℚ (Z.test.model.basis '' {i | j ≤ ω i})) →
      Z.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Z.test.test.orbit = 1 →
      ∀ η : Z.test.L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (Z.test.model.basis i)) ≤ p) →
      (∀ z ∈ Z.test.model.filtration.realification.subgroup (k + 1), ∀ x,
        Z.test.test.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * Z.test.test.observable x) →
      (∃ z ∈ Z.rank.realSubgroup (k + 1) (r + 1), realifyFunctional η z.coord ≠ 0) →
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) Z.test.eval →
      (Z.test.q : ℝ) < Real.exp (11 * p) →
      let A := (Finset.Ioc Z.test.U Z.test.V).filter (fun n => n % Z.test.q = Z.test.a.val)
      let F : ℕ → ℂ := fun n => Z.test.test.eval (fun _ => (n : ℤ))
      DenseTypeIPrefixes X X.sqrt A F (Real.exp (-20 * p)) →
      NativeTypeIOrbitFactors Z η (Q.eval₂ (Nat.castRingHom ℝ) p)

set_option maxRecDepth 2000 in
/-- Close the actual prepared Type I branch by the rank drop on its
normalized recovered factors. -/
theorem native_prime_prepared_typeI_branch_of_factors {k : ℕ}
    (h : NativePrimePreparedTypeIFactorRecovery k) : NativePrimePreparedTypeIBranch k := by
  obtain ⟨P, Q, hFactor⟩ := h
  obtain ⟨B, _, hDrop⟩ := nativeRankedPrimeTest_rank_drop_of_typeI_factors (k + 1) 19 (by omega)
  let T := Polynomial.X + Q
  let R := P + (T ^ B)
  obtain ⟨C, hC, hBudget⟩ := exists_prepared_branch_polynomial_budget R
  refine ⟨C, hC, 1 / 2, by norm_num, ?_⟩
  filter_upwards [hFactor, hDrop, eventually_gt_atTop (0 : ℕ)] with X hFactor hDrop hX
  intro r hr p hp hpX Z ω hω hNorm η hHeight hVertical hNonzero hCorr hq A F hcase
  let u := Q.eval₂ (Nat.castRingHom ℝ) p
  let t := p + u
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hP₀ := natPolynomial_eval₂_real_nonneg P hp₀
  have hu₀ : 0 ≤ u := natPolynomial_eval₂_real_nonneg Q hp₀
  have hpt : p ≤ t := le_add_of_nonneg_right hu₀
  have hut : u ≤ t := le_add_of_nonneg_left hp₀
  have ht₀ : 0 ≤ t := hp₀.trans hpt
  have hpoly : R.eval₂ (Nat.castRingHom ℝ) p = P.eval₂ (Nat.castRingHom ℝ) p + t ^ B := by
    simp [R, T, t, u, Polynomial.eval₂_pow]
  obtain ⟨hcost, hLength, hScale⟩ := hBudget hp₂ hpX
  rw [hpoly] at hcost hLength hScale
  have htC : t ^ B ≤ p ^ C := (le_add_of_nonneg_left hP₀).trans hcost
  have htX : t ^ B ≤ Real.log (X : ℝ) := (le_add_of_nonneg_left hP₀).trans hLength
  have hRecover : P.eval₂ (Nat.castRingHom ℝ) p + Real.log 4 ≤ Real.log (X : ℝ) / 4 := by
    linarith only [hScale, pow_nonneg ht₀ B]
  obtain ⟨W, htop, hBases, q, hq₀, hqBound, ε, K, U, γ, hK₀, hU₀, hε, hγ, hprod, hcoeff⟩ :=
    hFactor r hr p hp hRecover Z ω hω hNorm η hHeight hVertical hNonzero hCorr hq hcase
  let Z' : NativeRankedPrimeTest (k + 1) (r + 1) X t :=
    ⟨{ Z.test with complexity := Z.test.complexity.mono hpt }, Z.rank, Z.complexity.mono Z.rank hpt⟩
  let D := Z.test.model
  have hε' : CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
      (Real.exp ((t + 2) ^ (19 : ℕ))) ε.log :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr hX) hε
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hu₀]) (by linarith only [hut]) _))
  have hCorr' : Real.exp (-t) < intervalCorrelation X (strictVonMangoldtCramerDifference X) Z'.test.eval :=
    (Real.exp_le_exp.mpr (neg_le_neg hpt)).trans_lt hCorr
  have hBasis' (i : Fin (k + 1)) : ∃ b : Basis
      (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (i.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (i.val + 1)),
      ∀ j l, rationalLogHeight (D.basis.repr (b j : Z.test.L) l) ≤ t := by
    obtain ⟨b, hb⟩ := hBases i
    exact ⟨b, fun j l => (hb j l).trans hut⟩
  obtain ⟨G, hG⟩ := hDrop (hp.trans hpt) htX Z'
    (hq.le.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpt (by norm_num)))) W η
    (fun x hx _ => htop x hx) (fun z hz => hVertical z (Z.rank.realSubgroup_le_degree _ _ hz)) hBasis'
    q hq₀ (hqBound.trans (Real.exp_le_exp.mpr hut)) ε K U γ hK₀ hU₀ hε' hγ hprod hcoeff hCorr'
  obtain ⟨G', _, hG'⟩ := nativeRankedPrimeTest_promote_correlation htC G (strictVonMangoldtCramerDifference X) hG
  exact ⟨G', hG'⟩

end PrimeUniformity

#print axioms PrimeUniformity.native_prime_prepared_typeI_branch_of_factors
