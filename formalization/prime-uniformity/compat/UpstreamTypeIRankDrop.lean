import UpstreamFastRankLift
import UpstreamRankedFreezingBudget
import UpstreamVerticalDescent
import OAI.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds
import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

set_option maxRecDepth 2000 in
/-- The exact Type I decomposition, its bounded fast layer bases, and
top-frequency annihilation give a lower-rank test with a uniform budget. -/
theorem nativeRankedPrimeTest_rank_drop_of_typeI_factors (s k : ℕ) (hs : 1 ≤ s) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ᶠ X : ℕ in atTop,
      ∀ {r : ℕ} {p : ℝ},
        max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ A ≤ Real.log (X : ℝ) →
        ∀ (Z : NativeRankedPrimeTest s (r + 1) X p),
        let D := Z.test.model
        (Z.test.q : ℝ) ≤ Real.exp (11 * p) →
        ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (η : Z.test.L →ₗ[ℚ] ℚ),
        (∀ x ∈ D.filtration.gradedRefiltrationLayer W s,
          x ∈ Z.rank.filtration.layer s (r + 1) → η x = 0) →
        (∀ z ∈ Z.rank.realSubgroup s (r + 1), ∀ x,
          Z.test.test.observable (z • x) =
            CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
              Z.test.test.observable x) →
        (∀ i : Fin s,
          ∃ b : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (i.val + 1)))) ℚ
              (D.filtration.gradedRefiltrationLayer W (i.val + 1)),
            ∀ j l, rationalLogHeight (D.basis.repr (b j : Z.test.L) l) ≤ p) →
        ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        let w : Unit → ℕ := fun _ => 1
        ∀ ε K U ρ : D.filtration.realification.PolynomialOrbit w,
          D.filtration.realification.polynomialOrbitEval w 0 K = 1 →
          D.filtration.realification.polynomialOrbitEval w 0 U = 1 →
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
            (Real.exp ((p + 2) ^ k)) ε.log →
          CoefficientGrid (D.basis.baseChange ℝ) q ρ.log →
          ε * K * U * ρ = Z.test.test.orbit →
          (∀ i : Fin s,
            coefficients K.log (Finsupp.single () (i.val + 1)) ∈
              (Z.rank.filtration.layer (i.val + 1) 2).baseChange ℝ ∧
            coefficients U.log (Finsupp.single () (i.val + 1)) ∈
              D.filtration.realGradedRefiltrationLayer W (i.val + 1)) →
          Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) Z.test.eval →
          ∃ G : NativeRankedPrimeTest s r X (p ^ A),
            Real.exp (-(p ^ A)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval := by
  obtain ⟨C, _, hLift⟩ := exists_native_fast_rank_lift s
  obtain ⟨B, _, hDrop⟩ := nativeRankedPrimeTest_rank_drop_of_normalized_factors s k
  let T : Polynomial ℕ := Polynomial.X
  let P := T + (T + Polynomial.C C) ^ C
  obtain ⟨A, hA, hpower⟩ := exists_natPolynomial_eval_le_power (P ^ B)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hDrop, eventually_gt_atTop (0 : ℕ)] with X hDrop hX
  intro r p hp hpX Z D hZq W η hη hvertical hBasis q hq hqp w ε K U ρ hK₀ hU₀ hε hρ hprod hcoeff hlarge
  classical
  let S (i : Fin s) := fastRankLayer D Z.rank W (i.val + 1)
  have hSB (i : Fin s) : ∃ b : Basis (Fin (finrank ℚ (S i))) ℚ (S i),
      ∀ j l, rationalLogHeight (D.basis.repr (b j : Z.test.L) l) ≤ p := by
    obtain ⟨b, hb⟩ := hBasis i
    by_cases hs₂ : 2 ≤ s
    · exact exists_fastRankLayer_basis D Z.rank W hs₂ Z.complexity i b hb
    have hs₁ : s = 1 := by omega
    have hr := Z.rank.filtration.rank_le_degree
    have hi : i.val + 1 = s := by omega
    have hbot : Z.rank.filtration.layer (i.val + 1) 2 = ⊥ :=
      Z.rank.filtration.layer_eq_bot_of_past_top (Or.inr ⟨hi.symm, by omega⟩)
    have hS : S i = D.filtration.gradedRefiltrationLayer W (i.val + 1) := by
      change fastRankLayer D Z.rank W (i.val + 1) = _
      simp only [fastRankLayer, hbot, sup_bot_eq]
    rw [hS]
    exact ⟨b, hb⟩
  choose b hb using hSB
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hnorm : D.filtration.realification.polynomialOrbitEval w 0 (K * U) = 1 := by
    rw [map_mul, hK₀, hU₀, one_mul]
  have hmid : ∀ i : Fin s, coefficients (K * U).log (Finsupp.single () (i.val + 1)) ∈
      (S i).baseChange ℝ :=
    fastRank_product_coefficients D Z.rank W hs K U (fun i => (hcoeff i).1) (fun i => (hcoeff i).2)
  obtain ⟨E, RE, hRE, φ, _, hφ, _, g, _, heval, htop⟩ :=
    hLift D Z.rank W η hη (K * U) hnorm hp₀ Z.complexity b hb hmid
  let a := p + (p + C) ^ C
  have hpa : p ≤ a := le_add_of_nonneg_right (by positivity)
  have hEcap : (p + C) ^ C ≤ a := le_add_of_nonneg_left hp₀
  have haB : a ^ B ≤ p ^ A := by
    simpa [P, T, a, Polynomial.eval₂_pow] using hpower p hp₂
  let Z' : NativeRankedPrimeTest s (r + 1) X a :=
    ⟨{ Z.test with complexity := Z.test.complexity.mono hpa }, Z.rank, Z.complexity.mono Z.rank hpa⟩
  let co := D.filtration.realification.polynomialOrbitCoordinates w
  have hgrid : D.filtration.PolynomialRationalGrid D.basis w q (co ρ) :=
    (D.filtration.polynomialRationalGrid_iff_coefficients D.basis w q (co ρ)).mpr hρ
  have hslow : D.filtration.PolynomialSlowBound D.basis w (fun _ => (X : ℝ))
      (Real.exp ((a + 2) ^ k)) (co ε) :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr hX) hε
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith only [hpa]) k))
  have hproduct : co ε * co (K * U) * co ρ * D.filtration.realification.adaptedConstantGroupHom w 1 =
      co Z.test.test.orbit := by
    simpa only [map_one, mul_one, map_mul, mul_assoc] using congrArg co hprod
  have hEval' (n : ℤ) :
      D.filtration.adaptedPolynomialRealValueHom w (fun _ => (n : ℝ)) (co (K * U)) =
        D.filtration.realification.polynomialOrbitEval w (fun _ => n) (K * U) := by
    change D.filtration.realification.polynomialOrbitRealEval w (fun _ => (n : ℝ)) (K * U) = _
    exact D.filtration.realification.polynomialOrbitRealEval_integer w (K * U) (fun _ => n)
  let : TopologicalSpace (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) := realification_moduleTopology_t2 E.basis
  have hcorr : Real.exp (-a) < intervalCorrelation X (strictVonMangoldtCramerDifference X) Z'.test.eval :=
    (Real.exp_le_exp.mpr (neg_le_neg hpa)).trans_lt hlarge
  obtain ⟨G, hG⟩ := hDrop (L := SubspaceFreeLift.Algebra S (r + 1)) (r := r) (p := a)
    (hp.trans hpa) (haB.trans hpX) Z'
    (hZq.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpa (by norm_num))))
    E RE (hRE.mono RE hEcap) φ (fun i j => (hφ i j).trans hEcap) g η hvertical q hq
    (hqp.trans (Real.exp_le_exp.mpr hpa)) (co ε) (co (K * U)) (co ρ) 1 (Subgroup.one_mem _)
    hproduct hgrid hslow (fun n => (heval (fun _ => n)).trans (hEval' n).symm)
    (fun z hz => ⟨(htop z hz).1, (htop z hz).2.2⟩) hcorr
  let G' : NativeRankedPrimeTest s r X (p ^ A) :=
    ⟨{ G.test with complexity := G.test.complexity.mono haB }, G.rank, G.complexity.mono G.rank haB⟩
  exact ⟨G', (Real.exp_le_exp.mpr (neg_le_neg haB)).trans_lt hG⟩

end PrimeUniformity
