import PrimeUniformity.UpstreamTypeIFromVaughan

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

/-- Select bounded projected and ambient rows at every positive degree of
one common fast algebra. The bounds are uniform across the degrees. -/
theorem exists_native_typeI_common_rows
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
    (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (u : Fin n → D.filtration.AssociatedGraded)
    (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p P : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hRank : R.ComplexityLE p)
    (hHeight : ∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) k) ≤ P) :
    let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    let Q := 2 * P + Z
    let B := ⌈Real.exp (((Q + 1) + 2) ^ 7)⌉₊
    let w : Unit → ℕ := fun _ => 1
    let G := R.filtration
    let F := G.associatedDegree
    let hF' : ∀ d, F.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}) := fun d =>
      (congrArg (fun M : NilpotentLieFiltration V s => M.layer d) R.associated).trans (hF d)
    let W' : LieSubalgebra ℚ F.AssociatedGraded :=
      cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) R.associated.symm) W
    let α (j : Fin s) := typeIMonomial (j.val + 1)
    let d (j : Fin s) := Finsupp.weight w (α j)
    (∀ j : Fin s, ∃ e : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (j.val + 1)),
        ∀ i k, rationalLogHeight (D.basis.repr (e i : V) k) ≤ Z) ∧
    1 ≤ B ∧
    ∃ m : Fin s → ℕ, (∀ j, m j ≤ n) ∧
    ∃ row : ∀ j, Fin (m j) → (Fin 4 → G.HigherHorizontal (d j)) →ₗ[ℚ] ℚ,
    ∃ η : ∀ j, V →ₗ[ℚ] (Fin (m j) → ℚ),
      (∀ j i, G.layerHorizontalImage (F.gradedRefiltrationLayer W') typeISingleSlot
        (fun k x hx => typeISingleSlot_mem_rankOne G k x (F.gradedRefiltrationLayer_le W' k hx)) (d j) ≤
          LinearMap.ker (row j i)) ∧
      (∀ j i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row j i (G.projectedHorizontalSymbolCoefficient F typeISingleSlot
          (typeISingleSlot_mem_rankOne G) w (α j) (F.polynomialSymbolBasis D.basis ω hF' w z))) B) ∧
      (∀ j, LinearMap.ker (η j) = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔
        R.filtration.layer (j.val + 1) 2) ∧
      (∀ j a i, RationalHeightLE (η j (D.basis a) i) B) ∧
      ∀ (g : D.filtration.realification.PolynomialOrbit w) j i,
        let gRank : F.realification.PolynomialOrbit w := R.orbitEquiv w g
        projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G) w (α j) (row j i)
          (F.realSymbolOfPolynomial D.basis ω hF' w gRank.log) =
            realifyCoordinateMap (η j) (coefficients g.log (α j)) i := by
  classical
  intro Z Q B w G F hF' W' α d
  have hgen := exists_native_typeI_fast_layer_generators D R ω hF W u hu hp hP hn hRank hHeight
  have hZ : 0 ≤ Z := by
    change 0 ≤ p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    positivity
  have hZQ : Z ≤ Q := le_add_of_nonneg_left (by positivity : 0 ≤ 2 * P)
  have hQ : 0 ≤ Q := hZ.trans hZQ
  choose k hk v hspan hv using fun j : Fin s => (hgen j).2
  have hkQ (j : Fin s) : (k j : ℝ) ≤ Q := by
    have hkR : (k j : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk j
    exact hkR.trans ((mul_le_mul_of_nonneg_left hn (by norm_num)).trans
      (le_add_of_nonneg_right hZ))
  have hrow (j : Fin s) := exists_native_typeI_rows_of_fast_layer_generators D R ω hF W
    j (v j) (hspan j) hQ (hkQ j) (fun i a => (hv j i a).trans hZQ)
  choose B₀ hB₀ hBexp m hm row η hann hcolumn hker hcoord hread using hrow
  have hB (j : Fin s) : B₀ j ≤ B := Nat.cast_le.mp ((hBexp j).trans (Nat.le_ceil _))
  refine ⟨fun j => (hgen j).1, one_le_ceil_exp (((Q + 1) + 2) ^ 7), m, hm, row, η,
    hann, ?_, hker, ?_, ?_⟩
  · intro j i z
    exact (hcolumn j i z).mono (hB j)
  · intro j a i
    exact (hcoord j a i).mono (hB j)
  · intro g j i gRank
    have h := hread j g i
    change projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G) w (α j) (row j i)
      (F.realSymbolOfPolynomial D.basis ω hF' w (R.orbitEquiv w g).log) =
        realifyCoordinateMap (η j) (coefficients g.log (α j)) i at h ⊢
    exact h

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_common_rows
