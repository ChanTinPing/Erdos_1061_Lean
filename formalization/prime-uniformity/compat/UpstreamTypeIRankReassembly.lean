import OAI.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization
import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}

private theorem typeI_real_submodule_sup (V W : Submodule ℚ L) :
    (V ⊔ W).baseChange ℝ = V.baseChange ℝ ⊔ W.baseChange ℝ := by
  have hspan : Submodule.span ℚ ((V : Set L) ∪ (W : Set L)) = V ⊔ W := by
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq]
  rw [← hspan, Submodule.baseChange_span, Set.image_union, Submodule.span_union,
    ← Submodule.baseChange_span, ← Submodule.baseChange_span,
    Submodule.span_eq, Submodule.span_eq]

private theorem exists_typeI_orbit_of_coefficients (D : RationalFilteredNilmanifold L s n)
    (v : Fin s → ℝ ⊗[ℚ] L)
    (hv : ∀ d, v d ∈ D.filtration.realification.layer (d.val + 1)) :
    ∃ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      g.log = positiveUnivariate v ∧
      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1 := by
  have hadapt : D.filtration.realification.Adapted (fun _ : Unit => 1) (positiveUnivariate v) := by
    apply (D.filtration.realification.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hv d
  refine ⟨polynomialOrbitOfLog (positiveUnivariate v) hadapt, rfl, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
  rw [eval_zero_eq_coefficient, positiveUnivariate_zero]

/-- Lift a coefficient relation to an exact product of
normalized native polynomial orbits. The smooth and rational factors retain
the prescribed coefficients, and the remaining two factors lie in the
rank-two layers and the supplied degree layers respectively. -/
theorem exists_rank_two_reassembly_of_layers (D : RationalFilteredNilmanifold L s n)
    (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (A : Fin s → Submodule ℚ L)
    (hA : ∀ d, A d ≤ D.filtration.layer (d.val + 1))
    (e q : Fin s → ℝ ⊗[ℚ] L)
    (he : ∀ d, e d ∈ D.filtration.realification.layer (d.val + 1))
    (hq : ∀ d, q d ∈ D.filtration.realification.layer (d.val + 1))
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hsmooth : ∀ d, ‖(D.basis.baseChange ℝ).equivFun (e d)‖ ≤ M / H ^ (d.val + 1))
    (l : Fin s → ℕ) (hl : ∀ d, 0 < l d)
    (hgrid : ∀ d, (D.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (l d))
    (hres : ∀ d, coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d) ∈
      (A d ⊔ R.filtration.layer (d.val + 1) 2).baseChange ℝ) :
    let w : Unit → ℕ := fun _ => 1
    let m := ∏ d, l d
    0 < m ∧ (∀ d, l d ∣ m) ∧
    ∃ ε K U ρ : D.filtration.realification.PolynomialOrbit w,
      ε.log = positiveUnivariate e ∧ ρ.log = positiveUnivariate q ∧
      D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 ρ = 1 ∧
      CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => H) M ε.log ∧
      CoefficientGrid (D.basis.baseChange ℝ) m ρ.log ∧ ε * K * U * ρ = g ∧
      ∀ d : Fin s,
        coefficients K.log (Finsupp.single () (d.val + 1)) ∈
          (R.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
        coefficients U.log (Finsupp.single () (d.val + 1)) ∈
          (A d).baseChange ℝ := by
  classical
  intro w m
  have hsplit (d : Fin s) : coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d) ∈
      (A d).baseChange ℝ ⊔
        (R.filtration.layer (d.val + 1) 2).baseChange ℝ := by
    rw [← typeI_real_submodule_sup]
    exact hres d
  choose v hv k hk hsum using fun d => Submodule.mem_sup.mp (hsplit d)
  have hvLayer (d : Fin s) : v d ∈ D.filtration.realification.layer (d.val + 1) :=
    Submodule.baseChange_mono ℝ (hA d) (hv d)
  obtain ⟨ε, hε, hε0⟩ := exists_typeI_orbit_of_coefficients D e he
  obtain ⟨U, hU, hU0⟩ := exists_typeI_orbit_of_coefficients D v hvLayer
  obtain ⟨ρ, hρ, hρ0⟩ := exists_typeI_orbit_of_coefficients D q hq
  let α (d : Fin s) : Unit →₀ ℕ := Finsupp.single () (d.val + 1)
  have hweight (d : Fin s) : Finsupp.weight w (α d) = d.val + 1 := by
    simp [α, w, Finsupp.weight_single]
  have hcoeff (d : Fin s) : coefficients g.log (α d) -
      (coefficients ε.log (α d) +
        coefficients (1 : D.filtration.realification.PolynomialOrbit w).log (α d) +
        coefficients U.log (α d) + coefficients ρ.log (α d)) ∈
      (R.filtration.layer (Finsupp.weight w (α d)) 2).baseChange ℝ := by
    rw [hweight, hε, hU, hρ, show (1 : D.filtration.realification.PolynomialOrbit w).log = 0 from rfl]
    simp only [α, positiveUnivariate_coefficient, map_zero, Finsupp.zero_apply, add_zero]
    have heq : coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + v d + q d) = k d := by
      calc
        _ = (coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d)) - v d := by abel
        _ = k d := by rw [← hsum d]; abel
    rw [heq]
    exact hk d
  obtain ⟨K, hK0, hprod, hK⟩ := R.exists_polynomialOrbit_factorization_rank_two hs w α
    g ε 1 U ρ hg hε0 (map_one _) hU0 hρ0 hcoeff
  have hm : 0 < m := Finset.prod_pos (fun d _ => hl d)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  refine ⟨hm, hdiv, ε, K, U, ρ, hε, hρ, hε0, hK0, hU0, hρ0, ?_, ?_, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (D.basis.baseChange ℝ) e _ (fun _ => hH) hM
    intro d
    rw [monomialScale, Finsupp.prod_single_index
      (a := ()) (b := d.val + 1) (h := fun _ j => H ^ j) (pow_zero H)]
    exact hsmooth d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    intro d
    exact realDenominatorGrid_subset_of_dvd (hl d) (hdiv d) (hgrid d)
  · simpa only [mul_one] using hprod
  · intro d
    refine ⟨?_, ?_⟩
    · have h := hK d
      rw [hweight d] at h
      exact h
    · rw [hU, positiveUnivariate_coefficient]
      exact hv d

/-- Reassemble the Type I factors with the refiltered fast layers. -/
theorem exists_typeI_rank_two_reassembly (D : RationalFilteredNilmanifold L s n)
    (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (e q : Fin s → ℝ ⊗[ℚ] L)
    (he : ∀ d, e d ∈ D.filtration.realification.layer (d.val + 1))
    (hq : ∀ d, q d ∈ D.filtration.realification.layer (d.val + 1))
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hsmooth : ∀ d, ‖(D.basis.baseChange ℝ).equivFun (e d)‖ ≤ M / H ^ (d.val + 1))
    (l : Fin s → ℕ) (hl : ∀ d, 0 < l d)
    (hgrid : ∀ d, (D.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (l d))
    (hres : ∀ d, coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d) ∈
      (D.filtration.gradedRefiltrationLayer W (d.val + 1) ⊔
        R.filtration.layer (d.val + 1) 2).baseChange ℝ) :
    let w : Unit → ℕ := fun _ => 1
    let m := ∏ d, l d
    0 < m ∧ (∀ d, l d ∣ m) ∧
    ∃ ε K U ρ : D.filtration.realification.PolynomialOrbit w,
      ε.log = positiveUnivariate e ∧ ρ.log = positiveUnivariate q ∧
      D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
      D.filtration.realification.polynomialOrbitEval w 0 ρ = 1 ∧
      CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => H) M ε.log ∧
      CoefficientGrid (D.basis.baseChange ℝ) m ρ.log ∧ ε * K * U * ρ = g ∧
      ∀ d : Fin s,
        coefficients K.log (Finsupp.single () (d.val + 1)) ∈
          (R.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
        coefficients U.log (Finsupp.single () (d.val + 1)) ∈
          (D.filtration.gradedRefiltrationLayer W (d.val + 1)).baseChange ℝ :=
  exists_rank_two_reassembly_of_layers D R hs g hg (fun d => D.filtration.gradedRefiltrationLayer W (d.val + 1))
    (fun d => D.filtration.gradedRefiltrationLayer_le W (d.val + 1)) e q he hq hH hM hsmooth l hl hgrid hres

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeI_rank_two_reassembly
#print axioms PrimeUniformity.exists_rank_two_reassembly_of_layers
