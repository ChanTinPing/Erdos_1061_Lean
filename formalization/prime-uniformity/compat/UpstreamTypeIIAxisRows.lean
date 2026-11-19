import OAI.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight
import OAI.Combinatorics.Progressions.Estimates.RealProductInclusion
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace PrimeUniformity

set_option maxHeartbeats 350000

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration RationalFilteredNilmanifold

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n : ℕ}
  (D : RationalFilteredNilmanifold L s n)

local notation "F₂" => (NilpotentLieFiltration.pi (fun i => RationalFilteredNilmanifold.filtration (pairModels D D i)))

/-- The first coordinate axis in the native pair model. -/
def nativeTypeIIAxisLieHom : L →ₗ⁅ℚ⁆ PairAlgebra L L :=
  liePiSingle (M := BoolLieFamily L L) true

@[simp] theorem nativeTypeIIAxisLieHom_true (x : L) : nativeTypeIIAxisLieHom x true = x := rfl

@[simp] theorem nativeTypeIIAxisLieHom_false (x : L) : nativeTypeIIAxisLieHom x false = 0 := rfl

theorem nativeTypeIIAxisLieHom_mem_layer (d : ℕ) (x : L) (hx : x ∈ D.filtration.layer d) :
    nativeTypeIIAxisLieHom x ∈ (F₂).layer d := by
  change nativeTypeIIAxisLieHom x ∈
    (NilpotentLieFiltration.pi (fun i => (pairModels D D i).filtration)).layer d
  rw [NilpotentLieFiltration.mem_pi_layer]
  intro i
  cases i
  · change nativeTypeIIAxisLieHom x false ∈ D.filtration.layer d
    rw [nativeTypeIIAxisLieHom_false]
    exact Submodule.zero_mem _
  · change nativeTypeIIAxisLieHom x true ∈ D.filtration.layer d
    rwa [nativeTypeIIAxisLieHom_true]

/-- The fast Lie algebra on the axis is the pullback along the graded
inclusion. -/
noncomputable def nativeTypeIIAxisFast (W : LieSubalgebra ℚ (F₂).AssociatedGraded) :
    LieSubalgebra ℚ D.filtration.AssociatedGraded :=
  W.comap (D.filtration.associatedGradedMap F₂ nativeTypeIIAxisLieHom
    (nativeTypeIIAxisLieHom_mem_layer D))

theorem nativeTypeIIAxisFast_mem_layer_iff (W : LieSubalgebra ℚ (F₂).AssociatedGraded)
    (d : ℕ) (x : D.filtration.layer d) :
    (x : L) ∈ D.filtration.gradedRefiltrationLayer (nativeTypeIIAxisFast D W) d ↔
      nativeTypeIIAxisLieHom (x : L) ∈ (F₂).gradedRefiltrationLayer W d := by
  rw [D.filtration.mem_gradedRefiltrationLayer_iff (nativeTypeIIAxisFast D W) d x]
  rw [(F₂).mem_gradedRefiltrationLayer_iff W d
    ⟨nativeTypeIIAxisLieHom (x : L), nativeTypeIIAxisLieHom_mem_layer D d x x.property⟩]
  change D.filtration.associatedGradedMap F₂ nativeTypeIIAxisLieHom
    (nativeTypeIIAxisLieHom_mem_layer D) (D.filtration.associatedGradedPieceMap d x) ∈ W ↔ _
  rw [D.filtration.associatedGradedMap_piece]

/-- The signed pair frequency restricts to the single-axis frequency on the
refiltered fast subalgebra. -/
theorem nativeTypeIIAxisFast_top_zero (W : LieSubalgebra ℚ (F₂).AssociatedGraded)
    (η : L →ₗ[ℚ] ℚ)
    (hzero : ∀ z ∈ (F₂).gradedRefiltrationLayer W s, pairFrequency η (-η) z = 0) :
    ∀ x ∈ D.filtration.gradedRefiltrationLayer (nativeTypeIIAxisFast D W) s, η x = 0 := by
  intro x hx
  have hxs := D.filtration.gradedRefiltrationLayer_le (nativeTypeIIAxisFast D W) s hx
  have hy := (nativeTypeIIAxisFast_mem_layer_iff D W s ⟨x, hxs⟩).mp hx
  have h : η x + (-η) (0 : L) = 0 :=
    (pairFrequency_apply η (-η) (nativeTypeIIAxisLieHom x)).symm.trans (hzero _ hy)
  rwa [map_zero, add_zero] at h

variable {ι κ : Type*} (e : Basis ι ℚ L) (b : Basis κ ℚ (PairAlgebra L L))

/-- Transfer the native zero-one inclusion bounds to the chosen bases. -/
theorem nativeTypeIIAxisLieHom_basisChange_logHeight [Fintype ι] [Fintype κ]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hpair : (pi (pairModels D D)).GeometryComplexityLE p)
    (heH : ∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p)
    (hbH : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ p) :
    ∀ i j, rationalLogHeight (b.repr (nativeTypeIIAxisLieHom (e i)) j) ≤
      adaptedMarkedMapHeightBudget p := by
  apply markedMap_basisChange_logHeight D (pi (pairModels D D)) e b
    nativeTypeIIAxisLieHom.toLinearMap hp hD hpair heH hbH
  intro i j
  exact rationalLogHeight_le_of_height (productInclusion_matrix_height (pairModels D D) true i j)
    (by simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp)

/-- Restricting an annihilator after quotienting pulls back the fast
subspace enlarged by the kernel of the quotient. -/
theorem projected_axis_row_kernel
    {V P Q X : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup P] [Module ℚ P]
    [AddCommGroup Q] [Module ℚ Q] [AddCommGroup X] [Module ℚ X]
    (fast : Submodule ℚ V) (quotient : V →ₗ[ℚ] P) (axis : X →ₗ[ℚ] V)
    (rows : P →ₗ[ℚ] Q) (hrows : LinearMap.ker rows = fast.map quotient) :
    LinearMap.ker ((rows.comp quotient).comp axis) =
      (fast ⊔ LinearMap.ker quotient).comap axis := by
  rw [LinearMap.ker_comp, LinearMap.ker_comp, hrows, Submodule.comap_map_eq]

end PrimeUniformity

#print axioms PrimeUniformity.nativeTypeIIAxisFast_mem_layer_iff
#print axioms PrimeUniformity.nativeTypeIIAxisFast_top_zero
#print axioms PrimeUniformity.nativeTypeIIAxisLieHom_basisChange_logHeight
#print axioms PrimeUniformity.projected_axis_row_kernel
