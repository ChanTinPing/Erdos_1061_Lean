import UpstreamBranchBudget
import UpstreamPrimePreparedRankBranches
import UpstreamTypeIIRankDrop

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- The actual normalized Type II orbit factors and the bounded degree layers
and leading-bracket certificate for the middle orbit. -/
def NativeTypeIIOrbitFactors {s r X : ℕ} {p : ℝ}
    (Z : NativeRankedPrimeTest s (r + 1) X p) (η : Z.test.L →ₗ[ℚ] ℚ) (t : ℝ) : Prop :=
  let D := Z.test.model
  let w : Unit → ℕ := fun _ => 1
  ∃ (S : Fin s → Submodule ℚ Z.test.L) (b : ∀ i, Basis (Fin (finrank ℚ (S i))) ℚ (S i)),
    (∀ i : Fin s, S i ≤ D.filtration.layer (i.val + 1)) ∧
    (∀ j a i, rationalLogHeight (D.basis.repr (b j a : Z.test.L) i) ≤ t) ∧
    (∀ v : FreeMagma (SubspaceFreeLift.Alphabet S),
      lieTreeWeight (SubspaceFreeLift.weight S) v = s → v.length = r + 1 →
        η (lieTreeEval (fun i => (b i.1 i.2 : Z.test.L)) v) = 0) ∧
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp t ∧
      ∃ ε U ρ : D.filtration.realification.PolynomialOrbit w,
        D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
        CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
          (Real.exp ((t + 2) ^ (19 : ℕ))) ε.log ∧
        CoefficientGrid (D.basis.baseChange ℝ) q ρ.log ∧
        ε * U * ρ = Z.test.test.orbit ∧
        ∀ i : Fin s, coefficients U.log (Finsupp.single () (i.val + 1)) ∈ (S i).baseChange ℝ

/-- It suffices to recover the actual Type II factors at a polynomial
complexity when the recovery scale fits inside a quarter of the log length. -/
def NativePrimePreparedTypeIIFactorRecovery (k : ℕ) : Prop :=
  ∃ P Q : Polynomial ℕ, ∀ᶠ X : ℕ in atTop,
    ∀ r < k + 1, ∀ p : ℝ,
      max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p + Real.log 4 ≤ Real.log (X : ℝ) / 4 →
      ∀ W : NativeRankedPrimeTest (k + 1) (r + 1) X p,
      ∀ ω : Fin W.test.dim → ℕ,
      (∀ j, W.test.model.filtration.layer j =
        Submodule.span ℚ (W.test.model.basis '' {i | j ≤ ω i})) →
      W.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 W.test.test.orbit = 1 →
      ∀ η : W.test.L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (W.test.model.basis i)) ≤ p) →
      (∀ z ∈ W.test.model.filtration.realification.subgroup (k + 1), ∀ x,
        W.test.test.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * W.test.test.observable x) →
      (∃ z ∈ W.rank.realSubgroup (k + 1) (r + 1), realifyFunctional η z.coord ≠ 0) →
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.test.eval →
      (W.test.q : ℝ) < Real.exp (11 * p) →
      let A := (Finset.Ioc W.test.U W.test.V).filter (fun n => n % W.test.q = W.test.a.val)
      let F : ℕ → ℂ := fun n => W.test.test.eval (fun _ => (n : ℤ))
      (∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
        (X : ℝ) * Real.exp (-20 * p) <
          ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖) →
      NativeTypeIIOrbitFactors W η (Q.eval₂ (Nat.castRingHom ℝ) p)

set_option maxRecDepth 2000 in
/-- Polynomially controlled Type II factor recovery closes the actual
prepared Vaughan Type II branch. -/
theorem native_prime_prepared_typeII_branch_of_factors {k : ℕ}
    (h : NativePrimePreparedTypeIIFactorRecovery k) : NativePrimePreparedTypeIIBranch k := by
  obtain ⟨P, Q, hFactor⟩ := h
  obtain ⟨B, _, hDrop⟩ := nativeRankedPrimeTest_rank_drop_of_typeII_factors (k + 1) 19
  let T := Polynomial.X + Q
  let R := P + (T ^ B)
  obtain ⟨C, hC, hBudget⟩ := exists_prepared_branch_polynomial_budget R
  refine ⟨C, hC, 1 / 2, by norm_num, ?_⟩
  filter_upwards [hFactor, hDrop, eventually_gt_atTop (0 : ℕ)] with X hFactor hDrop hX
  intro r hr p hp hpX W ω hω hNorm η hHeight hVertical hNonzero hCorr hq A F hcase
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
  obtain ⟨S, b, hS, hb, htop, q, hq₀, hqBound, ε, U, ρ, hU₀, hε, hρ, hprod, hcoeff⟩ :=
    hFactor r hr p hp hRecover W ω hω hNorm η hHeight hVertical hNonzero hCorr hq hcase
  let W' : NativeRankedPrimeTest (k + 1) (r + 1) X t :=
    ⟨{ W.test with complexity := W.test.complexity.mono hpt }, W.rank, W.complexity.mono W.rank hpt⟩
  let D := W.test.model
  have hε' : CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
      (Real.exp ((t + 2) ^ (19 : ℕ))) ε.log :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr hX) hε
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hu₀]) (by linarith only [hut]) _))
  have hCorr' : Real.exp (-t) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W'.test.eval :=
    (Real.exp_le_exp.mpr (neg_le_neg hpt)).trans_lt hCorr
  obtain ⟨G, hG⟩ := hDrop (hp.trans hpt) htX W'
    (hq.le.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpt (by norm_num))))
    S b hS (fun j a i => (hb j a i).trans hut) η htop
    (fun z hz => hVertical z (W.rank.realSubgroup_le_degree _ _ hz))
    q hq₀ (hqBound.trans (Real.exp_le_exp.mpr hut)) ε U ρ hU₀ hε' hρ hprod hcoeff hCorr'
  obtain ⟨G', _, hG'⟩ := nativeRankedPrimeTest_promote_correlation htC G (strictVonMangoldtCramerDifference X) hG
  exact ⟨G', hG'⟩

end PrimeUniformity
