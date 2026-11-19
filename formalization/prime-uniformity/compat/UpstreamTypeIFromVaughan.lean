import PrimeUniformity.UpstreamTypeIRowLift
import OAI.Combinatorics.Progressions.Linear.RefiltrationLayerBasis
import OAI.Combinatorics.Progressions.Linear.RankHorizontalRepresentatives
import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization
import OAI.Combinatorics.Progressions.Linear.SplitPreimageSpanning
import OAI.Combinatorics.Progressions.Linear.RationalSpanCoordinates

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

/-- A common Type I fast algebra with a bounded generator table determines
bounded bases of its refiltered layers and bounded generators for their sums
with the rank-two layers. -/
theorem exists_native_typeI_fast_layer_generators
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r)
    (ω : Fin n → ℕ)
    (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (u : Fin n → D.filtration.AssociatedGraded)
    (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p P : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hRank : R.ComplexityLE p)
    (hHeight : ∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) k) ≤ P) :
    let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    ∀ j : Fin s,
      (∃ e : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
          (D.filtration.gradedRefiltrationLayer W (j.val + 1)),
        ∀ i k, rationalLogHeight (D.basis.repr (e i : V) k) ≤ Z) ∧
      ∃ m ≤ 2 * n, ∃ v : Fin m → V,
        Submodule.span ℚ (Set.range v) =
          D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔ R.filtration.layer (j.val + 1) 2 ∧
        ∀ i k, rationalLogHeight (D.basis.repr (v i) k) ≤ Z := by
  classical
  intro Z j
  have hdim : (Fintype.card (Fin n) : ℝ) ≤ P + 1 := by
    simpa only [Fintype.card_fin] using hn.trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨B, _, hB, hFast⟩ := D.filtration.exists_uniform_refiltration_layer_bases
    D.basis ω hF W u hu (one_le_ceil_exp P) (fun i k => rationalHeightLE_ceil_exp (hHeight i k))
    (by linarith only [hP] : 0 ≤ P + 1) hdim hdim (ceil_exp_le_exp_add_one hP)
  obtain ⟨e, he⟩ := hFast (j.val + 1)
  obtain ⟨a, ha⟩ := R.exists_rank_two_basis ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    (Nat.succ_pos j.val) hRank
  have heZ (i) (k : Fin n) : rationalLogHeight (D.basis.repr (e i : V) k) ≤ Z := by
    apply rationalLogHeight_le_of_height (he i k)
    exact hB.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hp))
  have hpZ : p ≤ Z := le_add_of_nonneg_right (by positivity)
  let I := Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1))) ⊕
    Fin (finrank ℚ (R.filtration.layer (j.val + 1) 2))
  let v₀ : I → V := Sum.elim (fun i => (e i : V)) (fun i => (a i : V))
  let f := Fintype.equivFin I
  let v : Fin (Fintype.card I) → V := v₀ ∘ f.symm
  have hRange : Set.range v = Set.range v₀ := by
    change Set.range (v₀ ∘ f.symm) = Set.range v₀
    rw [Set.range_comp, f.symm.surjective.range_eq, Set.image_univ]
  let : FiniteDimensional ℚ V := D.basis.finiteDimensional_of_finite
  have hdimV : finrank ℚ V = n := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hsubdim (B' : Submodule ℚ V) : finrank ℚ B' ≤ n := (Submodule.finrank_le B').trans_eq hdimV
  have hcard : Fintype.card I ≤ 2 * n := by
    change Fintype.card (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1))) ⊕
      Fin (finrank ℚ (R.filtration.layer (j.val + 1) 2))) ≤ 2 * n
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, two_mul]
    exact Nat.add_le_add (hsubdim _) (hsubdim _)
  refine ⟨⟨e, heZ⟩, Fintype.card I, hcard, v, ?_, ?_⟩
  · rw [hRange]
    change Submodule.span ℚ (Set.range (Sum.elim (fun i => (e i : V)) (fun i => (a i : V)))) = _
    rw [span_range_sumElim, span_submodule_basis _ e, span_submodule_basis _ a]
  · intro i k
    change rationalLogHeight (D.basis.repr (v₀ (f.symm i)) k) ≤ Z
    cases f.symm i with
    | inl i => exact heZ i k
    | inr i => exact (ha i k).trans hpZ

private theorem typeI_refiltered_layer_cast {V : Type*} [LieRing V] [LieAlgebra ℚ V]
    {s : ℕ} {F G : NilpotentLieFiltration V s} (h : F = G)
    (W : LieSubalgebra ℚ F.AssociatedGraded) (j : ℕ) :
    G.gradedRefiltrationLayer
      (cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) h) W) j =
      F.gradedRefiltrationLayer W j := by
  subst G
  rfl

/-- Choose bounded Type I rows from the generators of a native fast layer
plus the rank-two layer. Their ambient map has exactly that kernel, and
the rows read the original native orbit coefficients. -/
theorem exists_native_typeI_rows_of_fast_layer_generators
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n k : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r)
    (ω : Fin n → ℕ)
    (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (j : Fin s) (v : Fin k → V)
    (hspan : Submodule.span ℚ (Set.range v) =
      D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔ R.filtration.layer (j.val + 1) 2)
    {P : ℝ} (hP : 0 ≤ P) (hk : (k : ℝ) ≤ P)
    (hHeight : ∀ i a, rationalLogHeight (D.basis.repr (v i) a) ≤ P) :
    let w : Unit → ℕ := fun _ => 1
    let G := R.filtration
    let F := G.associatedDegree
    let α := typeIMonomial (j.val + 1)
    let d := Finsupp.weight w α
    let hF' : ∀ a, F.layer a = Submodule.span ℚ (D.basis '' {i | a ≤ ω i}) := fun a =>
      (congrArg (fun M : NilpotentLieFiltration V s => M.layer a) R.associated).trans (hF a)
    let W' : LieSubalgebra ℚ F.AssociatedGraded :=
      cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) R.associated.symm) W
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp (((P + 1) + 2) ^ 7) ∧
    ∃ m : ℕ, m ≤ n ∧
    ∃ row : Fin m → (Fin 4 → G.HigherHorizontal d) →ₗ[ℚ] ℚ,
    ∃ η : V →ₗ[ℚ] (Fin m → ℚ),
      (∀ i, G.layerHorizontalImage (F.gradedRefiltrationLayer W') typeISingleSlot
        (fun a x hx => typeISingleSlot_mem_rankOne G a x (F.gradedRefiltrationLayer_le W' a hx)) d ≤
          LinearMap.ker (row i)) ∧
      (∀ i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row i (G.projectedHorizontalSymbolCoefficient F typeISingleSlot
          (typeISingleSlot_mem_rankOne G) w α (F.polynomialSymbolBasis D.basis ω hF' w z))) B) ∧
      LinearMap.ker η = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔ R.filtration.layer (j.val + 1) 2 ∧
      (∀ a i, RationalHeightLE (η (D.basis a) i) B) ∧
      ∀ (g : D.filtration.realification.PolynomialOrbit w) i,
        let gRank : F.realification.PolynomialOrbit w := R.orbitEquiv w g
        projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G) w α (row i)
          (F.realSymbolOfPolynomial D.basis ω hF' w gRank.log) =
            realifyCoordinateMap η (coefficients g.log α) i := by
  intro w G F α d hF' W'
  have hd : d = j.val + 1 := typeIMonomial_weight _
  have hW (a : ℕ) : F.gradedRefiltrationLayer W' a = D.filtration.gradedRefiltrationLayer W a :=
    typeI_refiltered_layer_cast R.associated.symm W a
  have hspan' : Submodule.span ℚ (Set.range v) = F.gradedRefiltrationLayer W' d ⊔ G.layer d 2 := by
    rw [hW, hd]
    exact hspan
  have hk' : (Fintype.card (Fin k) : ℝ) ≤ P + 1 := by
    simpa only [Fintype.card_fin] using hk.trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨B, hB, hBexp, m, hm, row, η, hann, hcolumn, hker, hcoord, hread⟩ :=
    exists_typeI_bounded_rows_with_log_coordinates G D.basis ω hF' W' (j.val + 1) v
      hspan' (one_le_ceil_exp P) (fun i a => rationalHeightLE_ceil_exp (hHeight i a))
      (by linarith only [hP] : 0 ≤ P + 1) hk' (ceil_exp_le_exp_add_one hP)
  refine ⟨B, hB, hBexp, m, (by simpa only [Fintype.card_fin] using hm), row, η,
    hann, hcolumn, ?_, hcoord, ?_⟩
  · have hker' : LinearMap.ker η = F.gradedRefiltrationLayer W' d ⊔ G.layer d 2 := hker
    rw [hW, hd] at hker'
    exact hker'
  · intro g i gRank
    have hh := hread gRank i
    have hglog : gRank.log = g.log := R.orbitEquiv_log w g
    exact hh.trans (congrArg (fun p => realifyCoordinateMap η (coefficients p α) i) hglog)

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_fast_layer_generators
#print axioms PrimeUniformity.exists_native_typeI_rows_of_fast_layer_generators
