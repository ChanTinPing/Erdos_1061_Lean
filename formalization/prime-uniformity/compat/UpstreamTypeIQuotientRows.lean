import PrimeUniformity.UpstreamTypeIProjection
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

private def typeIHorizontalQuotientMap (G : DegreeRankLieFiltration L s r) (j : ℕ)
    (V : Submodule ℚ L) : G.HigherHorizontal j →ₗ[ℚ] L ⧸ (V ⊔ G.layer j 2) :=
  (G.higherHorizontalKernel j).liftQ
    ((V ⊔ G.layer j 2).mkQ.comp (G.layer j 1).subtype) (by
      intro x hx
      have hle : G.layer j 2 ≤ V ⊔ G.layer j 2 := le_sup_right
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hle hx))

private theorem typeIHorizontalQuotientMap_layerHorizontalMap
    (G : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ L)
    (hA : ∀ j x, x ∈ A j → ∀ i, typeISingleSlot x i ∈ G.layer j 1)
    (j : ℕ) (V : Submodule ℚ L) (x : A j) :
    typeIHorizontalQuotientMap G j V ((G.layerHorizontalMap A typeISingleSlot hA j x) 0) =
      (V ⊔ G.layer j 2).mkQ x.val := by
  change (V ⊔ G.layer j 2).mkQ (typeISingleSlot x.val 0) = _
  simp [typeISingleSlot]

/-- Choose fixed separating rows and their ambient quotient coordinates
from a bounded generator table for the fast layer plus the rank-two layer. -/
theorem exists_typeI_bounded_horizontal_rows_with_coordinates {ι κ : Type*}
    [Fintype ι] [Fintype κ]
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
      ∀ (x : F.layer j) i,
        row i (G.layerHorizontalMap F.layer typeISingleSlot (typeISingleSlot_mem_rankOne G) j x) =
          η x.val i := by
  classical
  intro w α j F V hspan H hH hheight p hp hκ hHexp
  obtain ⟨B, hB, hBexp, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp
    b (V ⊔ G.layer j 2) v hspan hH hheight hp hκ hHexp
  let qMap := typeIHorizontalQuotientMap G j V
  let row (i : Fin m) : (Fin 4 → G.HigherHorizontal j) →ₗ[ℚ] ℚ :=
    (f.coord i).comp (qMap.comp (LinearMap.proj 0))
  let η := f.equivFun.toLinearMap.comp (V ⊔ G.layer j 2).mkQ
  have hrow (A : ℕ → Submodule ℚ L)
      (hA : ∀ k x, x ∈ A k → ∀ i, typeISingleSlot x i ∈ G.layer k 1)
      (x : A j) (i : Fin m) :
      row i (G.layerHorizontalMap A typeISingleSlot hA j x) =
        f.repr ((V ⊔ G.layer j 2).mkQ x.val) i := by
    change f.repr (qMap ((G.layerHorizontalMap A typeISingleSlot hA j x) 0)) i = _
    exact congrArg (fun z => f.repr z i)
      (typeIHorizontalQuotientMap_layerHorizontalMap G A hA j V x)
  refine ⟨B, hB, hBexp, m, hm, row, η, ?_, ?_, ?_, fun k i => hf i k, ?_⟩
  · intro i x hx
    obtain ⟨y, rfl⟩ := hx
    have hle : V ≤ V ⊔ G.layer j 2 := le_sup_left
    have hq : (V ⊔ G.layer j 2).mkQ y.val = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hle y.property)
    rw [LinearMap.mem_ker, hrow, hq]
    simp
  · intro i z
    by_cases hz : z.val.1 = α
    · rw [F.polynomialSymbolBasis_apply, G.projectedHorizontalSymbolCoefficient_symbol, hrow]
      change RationalHeightLE (f.repr ((V ⊔ G.layer j 2).mkQ (coefficients
        ((F.adaptedMonomialBasis b ω hF w ⟨z.val, z.property.le⟩ : F.adaptedLieSubalgebra w) :
          VectorPolynomial Unit ℚ L) α)) i) B
      rw [F.adaptedMonomialBasis_coe, coefficients_monomial]
      simpa only [hz, Finsupp.single_eq_same] using hf i z.val.2
    · rw [projectedHorizontalCoefficient_basis_eq_zero G F typeISingleSlot
        (typeISingleSlot_mem_rankOne G) b ω hF w α z hz, map_zero]
      exact rationalHeightLE_zero hB
  · ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hq : (V ⊔ G.layer j 2).mkQ x = 0 := by
        apply f.equivFun.injective
        simpa only [η, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using h
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    · intro h
      have hq : (V ⊔ G.layer j 2).mkQ x = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr h
      simp [η, hq]
  · intro x i
    exact hrow F.layer (typeISingleSlot_mem_rankOne G) x i

/-- Choose fixed separating rows on the one nonzero Type I horizontal
slot, with bounded coefficients on the symbol basis, from a bounded
generator table for the fast layer plus the rank-two layer. -/
theorem exists_typeI_bounded_horizontal_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
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
      (∀ i, G.layerHorizontalImage (F.gradedRefiltrationLayer U) typeISingleSlot
        (fun k x hx => typeISingleSlot_mem_rankOne G k x (F.gradedRefiltrationLayer_le U k hx)) j ≤
          LinearMap.ker (row i)) ∧
      (∀ i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row i (G.projectedHorizontalSymbolCoefficient F typeISingleSlot
          (typeISingleSlot_mem_rankOne G) w α (F.polynomialSymbolBasis b ω hF w z))) B) ∧
      ∀ x : F.layer j,
        (∀ i, row i (G.layerHorizontalMap F.layer typeISingleSlot (typeISingleSlot_mem_rankOne G) j x) = 0) ↔
          x.val ∈ V ⊔ G.layer j 2 := by
  intro w α j F V hspan H hH hheight p hp hκ hHexp
  obtain ⟨B, hB, hBexp, m, hm, row, η, hann, hcolumns, hker, _, hrow⟩ :=
    exists_typeI_bounded_horizontal_rows_with_coordinates G b ω hF U d v
      hspan hH hheight hp hκ hHexp
  refine ⟨B, hB, hBexp, m, hm, row, hann, hcolumns, ?_⟩
  intro x
  constructor
  · intro hx
    have hz : η x.val = 0 := funext fun i => (hrow x i).symm.trans (hx i)
    have hk : x.val ∈ LinearMap.ker η := LinearMap.mem_ker.mpr hz
    rw [hker] at hk
    exact hk
  · intro hx i
    have hk : x.val ∈ LinearMap.ker η := by rw [hker]; exact hx
    exact (hrow x i).trans (congrFun (LinearMap.mem_ker.mp hk) i)

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeI_bounded_horizontal_rows
#print axioms PrimeUniformity.exists_typeI_bounded_horizontal_rows_with_coordinates
