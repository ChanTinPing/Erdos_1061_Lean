import UpstreamTypeIIPairedGenerators
import UpstreamTypeIIRowConstraints

namespace PrimeUniformity

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration RationalFilteredNilmanifold
open VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D D)))
local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))
local notation "hΦ" => (nativeTypeIIFourSlotMap_mem_layer D R)

/-- A common paired symbol factorization gives the actual near-integer rows
with their coordinate interpretation on the original orbit. -/
theorem exists_typeII_common_native_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hs : 1 ≤ s) (T : D.Niltest (fun _ : Unit => 1))
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ d, (F₂).layer d = Submodule.span ℚ (b '' {i | d ≤ ω i}))
    (W : LieSubalgebra ℚ (F₂).AssociatedGraded)
    (u : κ → (F₂).AssociatedGraded) (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {z : ℝ} (hz : 0 ≤ z) (hR : R.ComplexityLE z)
    (hPair : (pi (pairModels D D)).GeometryComplexityLE z)
    (hι : (Fintype.card ι : ℝ) ≤ z) (hκ : (Fintype.card κ : ℝ) ≤ z)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ z)
    (huH : ∀ i j, rationalLogHeight (((F₂).associatedGradedBasis b ω hF).repr (u i) j) ≤ z)
    (P : ℝ) (l : ℕ) (hl : 0 < l) (S : Finset (ℕ × ℕ))
    {Y : ℝ} (hY : 0 < Y)
    (hFac : ∀ v ∈ S,
      let V := T.scalarAffinePullback (v.1 : ℚ) (fun _ => 0)
      let V' := (T.scalarAffinePullback (v.2 : ℚ) (fun _ => 0)).conjugate
      (F₂).SymbolFactorizationIn b ω hF (fun _ => Y)
        (pairOrbitSymbol D D V.orbit V'.orbit b ω hF) P l W) :
    let N := Fintype.card ι * (s + 1) * 2 ^ s
    let A := (F₂).gradedRefiltrationLayer W
    let Bh := ⌈Real.exp (typeIIPairedAxisRowLogBudget z)⌉₊
    ∃ (B : ℕ) (J : Fin s → ℕ),
      1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((typeIIPairedGeneratorBudget z + 3) ^ 7 + 1) ∧
      (∀ d, J d ≤ Fintype.card ι) ∧
      ∃ (ξ : ∀ d, L →ₗ[ℚ] (Fin (J d) → ℚ)) (θ : ∀ d, Fin (J d) → Bool → ℝ)
        (m : ∀ d, Fin (J d) → ℕ),
        (∀ d, LinearMap.ker (ξ d) = nativeTypeIIAxisSaturatedLayer R.filtration A (d.val + 1)) ∧
        (∀ d k i, RationalHeightLE (ξ d (D.basis k) i) Bh) ∧
        (∀ d i, θ d i true = realifyCoordinateMap (ξ d)
          (coefficients T.orbit.log (Finsupp.single () (d.val + 1))) i) ∧
        (∀ d i, 0 < m d i ∧ m d i ≤ B ^ N * l) ∧
        ∀ v ∈ S, ∀ d i, ∃ a : ℤ,
          |((m d i : ℝ) * θ d i true) * (v.1 : ℝ) ^ (d.val + 1) +
            ((m d i : ℝ) * θ d i false) * (v.2 : ℝ) ^ (d.val + 1) - a| ≤
              ((l : ℝ) * (N : ℝ) * (B ^ N : ℕ) * Real.exp P) / Y ^ (d.val + 1) := by
  intro N A Bh
  obtain ⟨B, hB, hBexp, hRows⟩ := exists_typeII_bounded_paired_rows_from_common_fast
    D R F₂ b ω hF W hΦ u hu hz hR hPair hι hκ hb huH
  choose J hJ row ξ hann hcol _hPairKer hker _hPairHeight hξ hread using hRows
  obtain ⟨m, hm, hnear⟩ := exists_typeII_projected_rows_of_common_symbol_factors
    D R hs T b ω hF row W P l hl S (fun _ => Y) hY (fun _ _ => le_rfl) hB hFac hann hcol
  let w : Unit → ℕ := fun _ => 1
  let α (d : Fin s) := Finsupp.single () (d.val + 1)
  let θ (d : Fin s) (i : Fin (J d)) (k : Bool) :=
    projectedHorizontalRow R.filtration F₂ Φ hΦ w (α d) (row d i)
      (pairOrbitSymbol D D (if k then T.orbit else 1)
        (if k then 1 else T.orbit) b ω hF).coord
  refine ⟨B, J, hB, hBexp, hJ, fun d => (ξ d).comp nativeTypeIIAxisLieHom.toLinearMap, θ, m,
    hker, ?_, ?_, hm, hnear⟩
  · intro d k i
    exact rationalHeightLE_ceil_exp (hξ d k i)
  · intro d i
    exact native_typeII_axis_row_eq_orbit_coordinate D R T.orbit b ω hF (α d) (ξ d) i (row d i)
      (fun x => hread d x i) true

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeII_common_native_rows
