import PrimeUniformity.UpstreamTypeICommonRows
import PrimeUniformity.UpstreamTypeINativeFactorTransport
import PrimeUniformity.UpstreamTypeIRowRecovery

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

/-- An ambient rational measurement of the Type I horizontal quotient,
with common clearing multipliers and near-integer estimates on every
retained dilation. -/
def NativeTypeICommonNear {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (p P X : ℝ) (L l : ℕ) (S : Finset ℕ) : Prop :=
    let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    let B := ⌈Real.exp ((2 * P + Z + 1 + 2) ^ 7)⌉₊
    let N := n * (s + 1) * 2 ^ s
    let A := B ^ N
    let H := (l : ℝ) * N * A * Real.exp P
    (∀ j : Fin s, ∃ e : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (j.val + 1)),
        ∀ i k, rationalLogHeight (D.basis.repr (e i : V) k) ≤ Z) ∧
    1 ≤ B ∧
    ∃ m : Fin s → ℕ, (∀ j, m j ≤ n) ∧
    ∃ η : ∀ j, V →ₗ[ℚ] (Fin (m j) → ℚ),
      (∀ j, LinearMap.ker (η j) = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔
        R.filtration.layer (j.val + 1) 2) ∧
      (∀ j a i, RationalHeightLE (η j (D.basis a) i) B) ∧
    ∃ c : ∀ j, Fin (m j) → ℕ, (∀ j i, 0 < c j i ∧ c j i ≤ A * l) ∧
      ∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((c j i : ℝ) * realifyCoordinateMap (η j)
          (coefficients g.log (typeIMonomial (j.val + 1))) i) * (d : ℝ) ^ (j.val + 1) - a| ≤
            H / (X / L) ^ (j.val + 1)

set_option maxRecDepth 2000 in
/-- Actual affine-pullback factors imply the ambient Type I near-integer
conditions for one simultaneous collection of quotient rows. -/
theorem exists_native_typeI_near_of_common_factors
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (ω : Fin n → ℕ) (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (T : D.Niltest (fun _ : Unit => 1))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (u : Fin n → D.filtration.AssociatedGraded)
    (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p P : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hRank : R.ComplexityLE p)
    (hHeight : ∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) k) ≤ P)
    (L l : ℕ) {X H₀ : ℝ} (hl : 0 < l) (hY : 0 < X / L) (hSide : X / L ≤ H₀) (S : Finset ℕ)
    (hfactors : ∀ d ∈ S, D.filtration.SymbolFactorizationIn D.basis ω hF (fun _ : Unit => H₀)
      ((T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF) P l W) :
    NativeTypeICommonNear D R W T.orbit p P X L l S := by
  unfold NativeTypeICommonNear
  intro Z B N A H
  obtain ⟨hFast, hB, m, hm, row, η, hann, hcol, hker, hη, hread⟩ :=
    exists_native_typeI_common_rows D R ω hF W u hu hp hP hn hRank hHeight
  let w : Unit → ℕ := fun _ => 1
  let G := R.filtration
  let F := G.associatedDegree
  let hF' : ∀ d, F.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}) := fun d =>
    (congrArg (fun M : NilpotentLieFiltration V s => M.layer d) R.associated).trans (hF d)
  let W' : LieSubalgebra ℚ F.AssociatedGraded :=
    cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) R.associated.symm) W
  let gRank : F.realification.PolynomialOrbit w := R.orbitEquiv w T.orbit
  let Xg : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfPolynomial D.basis ω hF' w gRank.log⟩
  have hFac (d : ℕ) (hd : d ∈ S) : F.SymbolFactorizationIn D.basis ω hF' (fun _ : Unit => H₀)
      (F.realPolynomialSymbolDilationHom w (d : ℚ) Xg) P l W' :=
    native_typeI_pullback_factorization_for_rank_orbit D R ω hF T W d l H₀ P (hfactors d hd)
  obtain ⟨c, hc, hNear⟩ := exists_typeI_projected_rows_of_common_symbol_factors
    (J := fun j => Fin (m j)) G hs D.basis ω hF' gRank row W' P l hl S hY hSide hB hFac hann hcol
  refine ⟨hFast, hB, m, hm, η, hker, hη, c, ?_, ?_⟩
  · intro j i
    simpa only [A, N, Fintype.card_fin] using hc j i
  · intro d hd j i
    obtain ⟨a, ha⟩ := hNear d hd j i
    let σ := projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G) w
      (typeIMonomial (j.val + 1)) (row j i) Xg.coord
    let θ := realifyCoordinateMap (η j) (coefficients T.orbit.log (typeIMonomial (j.val + 1))) i
    let f (y : ℝ) := |((c j i : ℝ) * y) * (d : ℝ) ^ (j.val + 1) - (a : ℝ)|
    have heq := hread T.orbit j i
    change σ = θ at heq
    let Nsym := Fintype.card (Fin n) * (s + 1) * 2 ^ s
    let Hsym := (l : ℝ) * (Nsym : ℝ) * ((B ^ Nsym : ℕ) : ℝ) * Real.exp P
    change f σ ≤ Hsym / (X / L) ^ (j.val + 1) at ha
    have hH : Hsym = H := by simp only [Hsym, Nsym, H, A, N, Fintype.card_fin]
    have hbound := congrArg (fun y : ℝ => y / (X / L) ^ (j.val + 1)) hH
    refine ⟨a, ?_⟩
    change f θ ≤ H / (X / L) ^ (j.val + 1)
    exact (congrArg f heq).symm.le.trans (ha.trans hbound.le)

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_near_of_common_factors
