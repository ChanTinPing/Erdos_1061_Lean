import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

/-- For a normalized one-variable orbit, the refiltered-layer conditions on
the finitely many positive degrees imply the conditions on all monomials. -/
theorem native_fast_univariate_coefficients {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ i : Fin s,
      coefficients g.log (Finsupp.single () (i.val + 1)) ∈
        D.filtration.realGradedRefiltrationLayer W (i.val + 1)) :
    coefficients g.log 0 = 0 ∧
      ∀ α, coefficients g.log α ∈
        D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α) := by
  have hzero := congrArg NilpotentLieBCHGroup.coord hg
  change eval (fun _ : Unit => (0 : ℚ)) g.log = 0 at hzero
  rw [eval_zero_eq_coefficient] at hzero
  refine ⟨hzero, ?_⟩
  intro α
  let j := α ()
  have hα : Finsupp.single () j = α := by
    apply Finsupp.ext
    intro i
    cases i
    exact Finsupp.single_eq_same
  by_cases hj₀ : j = 0
  · rw [← hα, hj₀, Finsupp.single_zero, hzero]
    exact Submodule.zero_mem _
  by_cases hj : j ≤ s
  · let i : Fin s := ⟨j - 1, by omega⟩
    have hi : i.val + 1 = j := by
      change (j - 1) + 1 = j
      omega
    rw [← hα, ← hi, Finsupp.weight_single, smul_eq_mul, mul_one]
    exact hcoeff i
  · have hmem := (D.filtration.realification.adapted_iff_coefficients _ _).mp g.adapted α
    have hweight : Finsupp.weight (fun _ : Unit => 1) α = j := by
      rw [← hα, Finsupp.weight_single, smul_eq_mul, mul_one]
    rw [hweight, D.filtration.realification.layer_eq_bot_above_step (by omega : s < j),
      Submodule.mem_bot] at hmem
    rw [hmem]
    exact Submodule.zero_mem _

/-- Realize the actual normalized fast factor in a controlled native
refiltered model. The inclusion realizes the ambient polynomial values and
maps the top subgroup into the kernel of the ambient vertical frequency. -/
theorem exists_native_fast_orbit_realization :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) →
      ∀ (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
        (middle : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (_hcoeff : ∀ α, coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight w α))
        (_hzero : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
        (η : L →ₗ[ℚ] ℚ)
        (_hη : ∀ x ∈ W, basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω s x = x →
          D.filtration.gradedFrequency b ω hF η x = 0),
        ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
            (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
          E.filtration = D.filtration.gradedRefiltration W ∧
          E.lattice = D.lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
          E.GeometryComplexityLE ((p + C) ^ C) ∧
          (∀ i j, rationalLogHeight (D.basis.repr (E.basis i : L) j) ≤ (p + C) ^ C) ∧
          ∃ g : E.filtration.realification.PolynomialOrbit w,
            let Φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl
            (∀ x : σ → ℤ, Φ (E.filtration.realification.polynomialOrbitEval w x g) =
              D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) middle) ∧
            ∀ z ∈ E.filtration.realification.subgroup s,
              Φ z ∈ D.filtration.realification.subgroup s ∧
                realifyFunctional η (Φ z).coord = 0 := by
  obtain ⟨C, hC, hmodel⟩ := exists_controlled_adapted_refiltration_model
  refine ⟨C, hC, ?_⟩
  intro L κ σ _ _ _ s d n D b ω hF W v hspan p hp hD hκ hb hv w hw middle hcoeff hzero η hη
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel D b ω hF W v hspan hp hD hκ hb hv
  obtain ⟨g, hg⟩ := D.filtration.exists_model_refiltered_polynomial W E hEF w hw middle hcoeff hzero
  refine ⟨E, hEF, hEL, hE, hinc, g, hg, ?_⟩
  intro z hz
  let Φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
  have htop : (Φ z).coord ∈ D.filtration.realGradedRefiltrationLayer W s := by
    apply (D.filtration.mem_native_refiltration_layer W s z.coord).mp
    have hzLayer : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using hzLayer
  exact ⟨D.filtration.realGradedRefiltrationLayer_le W s htop,
    D.filtration.real_frequency_zero_on_refiltered_top b ω hF W η hη _ htop⟩

end PrimeUniformity
