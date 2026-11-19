import PrimeUniformity.UpstreamTypeIQuotientRows
import OAI.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

/-- A Type I row induced by an ambient quotient coordinate reads the same
real number from the polynomial symbol and from the original log coefficient. -/
theorem typeI_projected_row_eq_ambient_coordinate {σ ι J : Type*}
    (G : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ k, G.associatedDegree.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (η : L →ₗ[ℚ] (J → ℚ)) (i : J)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ)
    (hrow : ∀ x : G.associatedDegree.layer (Finsupp.weight w α),
      row (G.layerHorizontalMap G.associatedDegree.layer typeISingleSlot
        (typeISingleSlot_mem_rankOne G) (Finsupp.weight w α) x) = η x.val i)
    (p : G.associatedDegree.realification.adaptedLieSubalgebra w) :
    projectedHorizontalRow G G.associatedDegree typeISingleSlot (typeISingleSlot_mem_rankOne G)
      w α row (G.associatedDegree.realPolynomialSymbolMap b ω hF w p) =
        realifyCoordinateMap η (coefficients p.val α) i := by
  let F := G.associatedDegree
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedPolynomialTensor_coe,
    F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul, realifyCoordinateMap_tmul]
    let P := G.projectedHorizontalSymbolCoefficient F typeISingleSlot
      (typeISingleSlot_mem_rankOne G) w α
    change (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ)
      (row.baseChange ℝ (P.baseChange ℝ (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p))) = _
    simp only [LinearMap.baseChange_tmul, P, G.projectedHorizontalSymbolCoefficient_symbol,
      TensorProduct.AlgebraTensorModule.rid_tmul, Rat.smul_def, mul_comm]
    exact congrArg (fun z : ℚ => a * (z : ℝ)) (hrow ⟨coefficients p.val α, p.property α⟩)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, Pi.add_apply, hx, hy]

/-- Select the bounded horizontal rows and the ambient map together, with
their exact agreement on the log coefficients of every Type I orbit. -/
theorem exists_typeI_bounded_rows_with_log_coordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, G.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ G.associatedDegree.AssociatedGraded) (d : ℕ) (v : κ → L) :
    let w : Unit → ℕ := fun _ => 1
    let α := typeIMonomial d
    let j := Finsupp.weight w α
    let F := G.associatedDegree
    let V := F.gradedRefiltrationLayer U j
    Submodule.span ℚ (Set.range v) = V ⊔ G.layer j 2 →
    ∀ {H : ℕ}, 1 ≤ H → (∀ a i, RationalHeightLE (b.repr (v a) i) H) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card κ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
    ∃ m : ℕ, m ≤ Fintype.card ι ∧
    ∃ row : Fin m → (Fin 4 → G.HigherHorizontal j) →ₗ[ℚ] ℚ,
    ∃ η : L →ₗ[ℚ] (Fin m → ℚ),
      (∀ i, G.layerHorizontalImage (F.gradedRefiltrationLayer U) typeISingleSlot
        (fun k x hx => typeISingleSlot_mem_rankOne G k x (F.gradedRefiltrationLayer_le U k hx)) j ≤
          LinearMap.ker (row i)) ∧
      (∀ i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row i (G.projectedHorizontalSymbolCoefficient F typeISingleSlot
          (typeISingleSlot_mem_rankOne G) w α (F.polynomialSymbolBasis b ω hF w z))) B) ∧
      LinearMap.ker η = V ⊔ G.layer j 2 ∧
      (∀ k i, RationalHeightLE (η (b k) i) B) ∧
      ∀ (g : F.realification.PolynomialOrbit w) i,
        projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G) w α (row i)
          (F.realSymbolOfPolynomial b ω hF w g.log) =
            realifyCoordinateMap η (coefficients g.log α) i := by
  intro w α j F V hspan H hH hheight p hp hκ hHexp
  obtain ⟨B, hB, hBexp, m, hm, row, η, hann, hcolumns, hker, hcoordHeight, hrational⟩ :=
    exists_typeI_bounded_horizontal_rows_with_coordinates G b ω hF U d v
      hspan hH hheight hp hκ hHexp
  refine ⟨B, hB, hBexp, m, hm, row, η, hann, hcolumns, hker, hcoordHeight, ?_⟩
  intro g i
  let P : F.realification.adaptedLieSubalgebra w :=
    ⟨g.log, (F.realification.mem_adaptedSubmodule w g.log).mpr g.adapted⟩
  exact typeI_projected_row_eq_ambient_coordinate G b ω hF w α η i (row i)
    (fun x => hrational x i) P

end PrimeUniformity

#print axioms PrimeUniformity.typeI_projected_row_eq_ambient_coordinate
#print axioms PrimeUniformity.exists_typeI_bounded_rows_with_log_coordinates
