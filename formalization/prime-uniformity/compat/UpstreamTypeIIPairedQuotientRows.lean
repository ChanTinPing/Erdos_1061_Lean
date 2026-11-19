import UpstreamTypeIIAxisSaturation
import PrimeUniformity.UpstreamTypeIISymbols
import OAI.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))

private def nativeTypeIIOppositeAxis : L →ₗ⁅ℚ⁆ PairAlgebra L L :=
  liePiSingle (M := BoolLieFamily L L) false

private def typeIIHorizontalComponentQuotient
    (G : DegreeRankLieFiltration L s r) (j : ℕ) (V : Submodule ℚ (PairAlgebra L L))
    (T : L →ₗ[ℚ] PairAlgebra L L) (hT : ∀ x ∈ G.layer j 2, T x ∈ nativeTypeIIPairRankTwo G j) :
    G.HigherHorizontal j →ₗ[ℚ] (PairAlgebra L L ⧸ (V ⊔ nativeTypeIIPairRankTwo G j)) :=
  (G.higherHorizontalKernel j).liftQ
    (((V ⊔ nativeTypeIIPairRankTwo G j).mkQ.comp T).comp (G.layer j 1).subtype)
    (by
      intro x hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (show nativeTypeIIPairRankTwo G j ≤ V ⊔ nativeTypeIIPairRankTwo G j from le_sup_right)
        (hT x.val hx))

private def typeIIPairedHorizontalQuotient
    (G : DegreeRankLieFiltration L s r) (j : ℕ) (V : Submodule ℚ (PairAlgebra L L)) :
    (Fin 4 → G.HigherHorizontal j) →ₗ[ℚ] (PairAlgebra L L ⧸ (V ⊔ nativeTypeIIPairRankTwo G j)) :=
  (typeIIHorizontalComponentQuotient G j V nativeTypeIIAxisLieHom.toLinearMap
    (fun _ hx => ⟨hx, Submodule.zero_mem _⟩)).comp (LinearMap.proj 0) +
  (typeIIHorizontalComponentQuotient G j V nativeTypeIIOppositeAxis.toLinearMap
    (fun _ hx => ⟨Submodule.zero_mem _, hx⟩)).comp (LinearMap.proj 2)

private theorem typeIIPairedHorizontalQuotient_layerHorizontalMap
    (G : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ (PairAlgebra L L))
    (hA : ∀ j x, x ∈ A j → ∀ i, Φ x i ∈ G.layer j 1)
    (j : ℕ) (V : Submodule ℚ (PairAlgebra L L)) (x : A j) :
    typeIIPairedHorizontalQuotient G j V (G.layerHorizontalMap A Φ hA j x) =
      (V ⊔ nativeTypeIIPairRankTwo G j).mkQ x.val := by
  let K := V ⊔ nativeTypeIIPairRankTwo G j
  change K.mkQ (nativeTypeIIAxisLieHom (nativeTypeIIFirstProjection x.val)) +
    K.mkQ (nativeTypeIIOppositeAxis (nativeTypeIISecondProjection x.val)) = K.mkQ x.val
  rw [← map_add]
  apply congrArg K.mkQ
  funext i
  cases i
  · change (0 : L) + nativeTypeIISecondProjection x.val = nativeTypeIISecondProjection x.val
    exact zero_add _
  · change nativeTypeIIFirstProjection x.val + (0 : L) = nativeTypeIIFirstProjection x.val
    exact add_zero _

/-- Choose horizontal rows that read the ambient paired quotient coordinates.
The ambient map has exactly the saturated paired fast layer as its kernel. -/
theorem exists_typeII_bounded_horizontal_rows_with_coordinates {σ ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration (PairAlgebra L L) s)
    (hΦ : ∀ j x, x ∈ F.layer j → ∀ i, Φ x i ∈ G.layer j 1)
    (A : ℕ → Submodule ℚ (PairAlgebra L L)) (hA : ∀ j, A j ≤ F.layer j)
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (v : κ → PairAlgebra L L) :
    let j := Finsupp.weight w α
    let K := A j ⊔ nativeTypeIIPairRankTwo G j
    Submodule.span ℚ (Set.range v) = K →
    ∀ {H : ℕ}, 1 ≤ H → (∀ a i, RationalHeightLE (b.repr (v a) i) H) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card κ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
    ∃ m : ℕ, m ≤ Fintype.card ι ∧
    ∃ row : Fin m → (Fin 4 → G.HigherHorizontal j) →ₗ[ℚ] ℚ,
    ∃ ξ : PairAlgebra L L →ₗ[ℚ] (Fin m → ℚ),
      (∀ i, G.layerHorizontalImage A Φ (fun k x hx => hΦ k x (hA k hx)) j ≤
        LinearMap.ker (row i)) ∧
      (∀ i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row i (G.projectedHorizontalSymbolCoefficient F Φ hΦ w α (F.polynomialSymbolBasis b ω hF w z))) B) ∧
      LinearMap.ker ξ = K ∧
      LinearMap.ker (ξ.comp nativeTypeIIAxisLieHom.toLinearMap) = nativeTypeIIAxisSaturatedLayer G A j ∧
      (∀ k i, RationalHeightLE (ξ (b k) i) B) ∧
      ∀ (x : F.layer j) i, row i (G.layerHorizontalMap F.layer Φ hΦ j x) = ξ x.val i := by
  classical
  intro j K hspan H hH hheight p hp hκ hHexp
  obtain ⟨B, hB, hBexp, m, hm, f, hf⟩ :=
    exists_submodule_quotient_basis_exp b K v hspan hH hheight hp hκ hHexp
  let qMap := typeIIPairedHorizontalQuotient G j (A j)
  let row (i : Fin m) := (f.coord i).comp qMap
  let ξ := f.equivFun.toLinearMap.comp K.mkQ
  have hrow (A' : ℕ → Submodule ℚ (PairAlgebra L L))
      (hA' : ∀ k x, x ∈ A' k → ∀ i, Φ x i ∈ G.layer k 1)
      (x : A' j) (i : Fin m) :
      row i (G.layerHorizontalMap A' Φ hA' j x) = ξ x.val i := by
    change f.repr (qMap (G.layerHorizontalMap A' Φ hA' j x)) i = f.repr (K.mkQ x.val) i
    exact congrArg (fun z => f.repr z i)
      (typeIIPairedHorizontalQuotient_layerHorizontalMap G A' hA' j (A j) x)
  have hker : LinearMap.ker ξ = K := by
    ext x
    rw [LinearMap.mem_ker]
    change f.equivFun (K.mkQ x) = 0 ↔ x ∈ K
    rw [f.equivFun.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero K
  have haxis : LinearMap.ker (ξ.comp nativeTypeIIAxisLieHom.toLinearMap) =
      nativeTypeIIAxisSaturatedLayer G A j := by
    rw [LinearMap.ker_comp, hker] <;> rfl
  refine ⟨B, hB, hBexp, m, hm, row, ξ, ?_, ?_, hker, haxis, (fun k i => hf i k), ?_⟩
  · intro i x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y.val ∈ LinearMap.ker ξ := by
      rw [hker]
      exact (show A j ≤ K from le_sup_left) y.property
    rw [LinearMap.mem_ker, hrow A (fun k z hz => hΦ k z (hA k hz))]
    exact congrFun (LinearMap.mem_ker.mp hy) i
  · intro i z
    by_cases hz : z.val.1 = α
    · rw [F.polynomialSymbolBasis_apply, G.projectedHorizontalSymbolCoefficient_symbol, hrow F.layer hΦ]
      change RationalHeightLE (f.repr (K.mkQ (coefficients
        ((F.adaptedMonomialBasis b ω hF w ⟨z.val, z.property.le⟩ : F.adaptedLieSubalgebra w) :
          VectorPolynomial σ ℚ (PairAlgebra L L)) α)) i) B
      rw [F.adaptedMonomialBasis_coe, coefficients_monomial]
      simpa only [hz, Finsupp.single_eq_same] using hf i z.val.2
    · rw [projectedHorizontalCoefficient_basis_eq_zero G F Φ hΦ b ω hF w α z hz, map_zero]
      exact rationalHeightLE_zero hB
  · exact hrow F.layer hΦ

/-- An ambient quotient coordinate reads the same real value from a row of
the paired symbol and from the corresponding original log coefficient. -/
theorem typeII_projected_row_eq_ambient_coordinate {σ ι J : Type*}
    (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration (PairAlgebra L L) s)
    (hΦ : ∀ j x, x ∈ F.layer j → ∀ i, Φ x i ∈ G.layer j 1)
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (ξ : PairAlgebra L L →ₗ[ℚ] (J → ℚ)) (i : J)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ)
    (hrow : ∀ x : F.layer (Finsupp.weight w α),
      row (G.layerHorizontalMap F.layer Φ hΦ (Finsupp.weight w α) x) = ξ x.val i)
    (p : F.realification.adaptedLieSubalgebra w) :
    projectedHorizontalRow G F Φ hΦ w α row (F.realPolynomialSymbolMap b ω hF w p) =
      realifyCoordinateMap ξ (coefficients p.val α) i := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedPolynomialTensor_coe,
    F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul, realifyCoordinateMap_tmul]
    let P := G.projectedHorizontalSymbolCoefficient F Φ hΦ w α
    change (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ)
      (row.baseChange ℝ (P.baseChange ℝ (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p))) = _
    simp only [LinearMap.baseChange_tmul, P, G.projectedHorizontalSymbolCoefficient_symbol,
      TensorProduct.AlgebraTensorModule.rid_tmul, Rat.smul_def, mul_comm]
    exact congrArg (fun z : ℚ => a * (z : ℝ)) (hrow ⟨coefficients p.val α, p.property α⟩)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, Pi.add_apply, hx, hy]

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeII_bounded_horizontal_rows_with_coordinates
#print axioms PrimeUniformity.typeII_projected_row_eq_ambient_coordinate
