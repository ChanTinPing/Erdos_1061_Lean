import UpstreamTypeIIPairedQuotientRows

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped BigOperators TensorProduct

universe u

private theorem realProductSingle_eq_liePiSingle_baseChange {I : Type*} {M : I → Type*}
    [∀ k, LieRing (M k)] [∀ k, LieAlgebra ℚ (M k)] [dec : DecidableEq I] (k : I) :
    realProductSingle (L := M) k = (liePiSingle (M := M) k).toLinearMap.baseChange ℝ := by
  let realSingle (d : DecidableEq I) := by
    letI : DecidableEq I := d
    exact (LinearMap.single ℚ M k).baseChange ℝ
  change realSingle (Classical.decEq I) = realSingle dec
  exact congrArg realSingle (Subsingleton.elim _ _)

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n : ℕ}
    (D : RationalFilteredNilmanifold L s n)
    {σ ι : Type*} {w : σ → ℕ}

/-- The true axis is the first component and the false axis is the second. -/
def nativeTypeIIRowAxis (k : Bool) : L →ₗ⁅ℚ⁆ PairAlgebra L L :=
  match k with
  | true => nativeTypeIIAxisLieHom
  | false => liePiSingle (M := BoolLieFamily L L) false

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D D)))

private theorem native_typeII_pairOrbit_log_sum
    (p q : D.filtration.realification.PolynomialOrbit w) :
    (pairOrbit D D p q).log =
      VectorPolynomial.map (((nativeTypeIIRowAxis true).toLinearMap.baseChange ℝ).restrictScalars ℚ) p.log +
      VectorPolynomial.map (((nativeTypeIIRowAxis false).toLinearMap.baseChange ℝ).restrictScalars ℚ) q.log := by
  let inputs (i : Bool) : (pairModels D D i).filtration.realification.PolynomialOrbit w := by
    cases i
    · exact q
    · exact p
  change (∑ i : Bool, VectorPolynomial.map
    ((realProductSingle (L := BoolLieFamily L L) i).restrictScalars ℚ) (inputs i).log) = _
  have ht : realProductSingle (L := BoolLieFamily L L) true =
      (nativeTypeIIRowAxis true).toLinearMap.baseChange ℝ :=
    realProductSingle_eq_liePiSingle_baseChange (M := BoolLieFamily L L) true
  have hf : realProductSingle (L := BoolLieFamily L L) false =
      (nativeTypeIIRowAxis false).toLinearMap.baseChange ℝ :=
    realProductSingle_eq_liePiSingle_baseChange (M := BoolLieFamily L L) false
  rw [Fintype.sum_bool]
  change VectorPolynomial.map ((realProductSingle (L := BoolLieFamily L L) true).restrictScalars ℚ) p.log +
      VectorPolynomial.map ((realProductSingle (L := BoolLieFamily L L) false).restrictScalars ℚ) q.log = _
  rw [ht, hf]
  rfl

/-- Taking a coefficient of the undilated orbit on one pair axis agrees
with applying the realified axis inclusion to the original coefficient. -/
theorem native_typeII_pair_axis_log_coefficient (g : D.filtration.realification.PolynomialOrbit w)
    (α : σ →₀ ℕ) (k : Bool) :
    coefficients (pairOrbit D D (if k then g else 1) (if k then 1 else g)).log α =
      ((nativeTypeIIRowAxis k).toLinearMap.baseChange ℝ) (coefficients g.log α) := by
  have hzero : (1 : D.filtration.realification.PolynomialOrbit w).log = 0 := rfl
  cases k
  · change coefficients (pairOrbit D D 1 g).log α = _
    rw [native_typeII_pairOrbit_log_sum D, hzero, map_zero, zero_add, coefficients_map,
      LinearMap.restrictScalars_apply]
  · change coefficients (pairOrbit D D g 1).log α = _
    rw [native_typeII_pairOrbit_log_sum D, hzero, map_zero, add_zero, coefficients_map,
      LinearMap.restrictScalars_apply]

variable {r : ℕ} (R : D.DegreeRankStructure r)

local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))
local notation "hΦ" => (nativeTypeIIFourSlotMap_mem_layer D R)

/-- Each axis row of the undilated paired symbol reads an ambient
coordinate of the original orbit's log coefficient. -/
theorem native_typeII_axis_row_eq_orbit_coordinate {J : Type*}
    (g : D.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ j, (F₂).layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (α : σ →₀ ℕ) (ξ : PairAlgebra L L →ₗ[ℚ] (J → ℚ)) (i : J)
    (row : (Fin 4 → R.filtration.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ)
    (hread : ∀ x : (F₂).layer (Finsupp.weight w α),
      row (R.filtration.layerHorizontalMap (F₂).layer Φ hΦ (Finsupp.weight w α) x) = ξ x.val i)
    (k : Bool) :
    projectedHorizontalRow R.filtration F₂ Φ hΦ w α row
      (pairOrbitSymbol D D (if k then g else 1) (if k then 1 else g) b ω hF).coord =
        realifyCoordinateMap (ξ.comp (nativeTypeIIRowAxis k).toLinearMap) (coefficients g.log α) i := by
  let Q := pairOrbit D D (if k then g else 1) (if k then 1 else g)
  let p : (F₂).realification.adaptedLieSubalgebra w :=
    ⟨Q.log, ((F₂).realification.mem_adaptedSubmodule w Q.log).mpr Q.adapted⟩
  have h := typeII_projected_row_eq_ambient_coordinate R.filtration F₂ hΦ b ω hF w α ξ i row hread p
  change projectedHorizontalRow R.filtration F₂ Φ hΦ w α row
    (pairOrbitSymbol D D (if k then g else 1) (if k then 1 else g) b ω hF).coord =
      realifyCoordinateMap ξ (coefficients Q.log α) i at h
  rw [realifyCoordinateMap_comp, ← native_typeII_pair_axis_log_coefficient D g α k]
  exact h

end PrimeUniformity

#print axioms PrimeUniformity.native_typeII_pair_axis_log_coefficient
#print axioms PrimeUniformity.native_typeII_axis_row_eq_orbit_coordinate
