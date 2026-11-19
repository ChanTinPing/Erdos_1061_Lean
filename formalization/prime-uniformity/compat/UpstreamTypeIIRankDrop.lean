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
/-- The normalized Type II factors yield a lower-rank test when the
frequency vanishes on the top degree and rank brackets of the bounded
middle-layer basis vectors. -/
theorem nativeRankedPrimeTest_rank_drop_of_typeII_factors (s k : ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ᶠ X : ℕ in atTop,
      ∀ {r : ℕ} {p : ℝ},
        max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ A ≤ Real.log (X : ℝ) →
        ∀ (Z : NativeRankedPrimeTest s (r + 1) X p),
        let D := Z.test.model
        (Z.test.q : ℝ) ≤ Real.exp (11 * p) →
        ∀ (S : Fin s → Submodule ℚ Z.test.L)
          (b : ∀ i, Basis (Fin (finrank ℚ (S i))) ℚ (S i)),
        (∀ i : Fin s, S i ≤ D.filtration.layer (i.val + 1)) →
        (∀ j a i, rationalLogHeight (D.basis.repr (b j a : Z.test.L) i) ≤ p) →
        ∀ (η : Z.test.L →ₗ[ℚ] ℚ),
        (∀ t : FreeMagma (SubspaceFreeLift.Alphabet S),
          lieTreeWeight (SubspaceFreeLift.weight S) t = s → t.length = r + 1 →
            η (lieTreeEval (fun i => (b i.1 i.2 : Z.test.L)) t) = 0) →
        (∀ z ∈ Z.rank.realSubgroup s (r + 1), ∀ x,
          Z.test.test.observable (z • x) =
            CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
              Z.test.test.observable x) →
        ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        let w : Unit → ℕ := fun _ => 1
        ∀ ε U ρ : D.filtration.realification.PolynomialOrbit w,
          D.filtration.realification.polynomialOrbitEval w 0 U = 1 →
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (X : ℝ))
            (Real.exp ((p + 2) ^ k)) ε.log →
          CoefficientGrid (D.basis.baseChange ℝ) q ρ.log →
          ε * U * ρ = Z.test.test.orbit →
          (∀ i : Fin s, coefficients U.log (Finsupp.single () (i.val + 1)) ∈ (S i).baseChange ℝ) →
          Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) Z.test.eval →
          ∃ G : NativeRankedPrimeTest s r X (p ^ A),
            Real.exp (-(p ^ A)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval := by
  obtain ⟨C, _, hLift⟩ := exists_native_rank_lift s
  obtain ⟨B, _, hDrop⟩ := nativeRankedPrimeTest_rank_drop_of_normalized_factors s k
  let T : Polynomial ℕ := Polynomial.X
  let P := T + (T + Polynomial.C C) ^ C
  obtain ⟨A, hA, hpower⟩ := exists_natPolynomial_eval_le_power (P ^ B)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hDrop, eventually_gt_atTop (0 : ℕ)] with X hDrop hX
  intro r p hp hpX Z D hZq S b hS hb η hη hvertical q hq hqp w ε U ρ hU₀ hε hρ hprod hcoeff hlarge
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hSR (i : Fin s) : S i ≤ Z.rank.filtration.layer (i.val + 1) 0 := by
    change S i ≤ Z.rank.filtration.associatedDegree.layer (i.val + 1)
    rw [Z.rank.associated]
    exact hS i
  obtain ⟨E, RE, hRE, φ, _, hφ, _, g, _, heval, htop⟩ :=
    hLift D Z.rank S b hSR η hη U hU₀ hp₀ Z.complexity hb hcoeff
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
  have hproduct : co ε * co U * co ρ * D.filtration.realification.adaptedConstantGroupHom w 1 =
      co Z.test.test.orbit := by
    simpa only [map_one, mul_one, map_mul] using congrArg co hprod
  have hEval' (n : ℤ) :
      D.filtration.adaptedPolynomialRealValueHom w (fun _ => (n : ℝ)) (co U) =
        D.filtration.realification.polynomialOrbitEval w (fun _ => n) U := by
    change D.filtration.realification.polynomialOrbitRealEval w (fun _ => (n : ℝ)) U = _
    exact D.filtration.realification.polynomialOrbitRealEval_integer w U (fun _ => n)
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
    (hqp.trans (Real.exp_le_exp.mpr hpa)) (co ε) (co U) (co ρ) 1 (Subgroup.one_mem _)
    hproduct hgrid hslow (fun n => (heval (fun _ => n)).trans (hEval' n).symm)
    (fun z hz => ⟨(htop z hz).1, (htop z hz).2.2⟩) hcorr
  let G' : NativeRankedPrimeTest s r X (p ^ A) :=
    ⟨{ G.test with complexity := G.test.complexity.mono haB }, G.rank, G.complexity.mono G.rank haB⟩
  exact ⟨G', (Real.exp_le_exp.mpr (neg_le_neg haB)).trans_lt hG⟩

end PrimeUniformity
