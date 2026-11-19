import PrimeUniformity.UpstreamTypeIIProjection
import OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold VectorPolynomial
open scoped BigOperators TensorProduct

universe u

section PairAxes

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    {σ ι : Type*} {w : σ → ℕ}

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D E)))

/-- The two coordinate axes give an exact additive splitting of the
logarithm of a product orbit. -/
theorem native_pairOrbit_log_add_axes
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    (pairOrbit D E p q).log = (pairOrbit D E p 1).log + (pairOrbit D E 1 q).log := by
  have h₁ : (1 : D.filtration.realification.PolynomialOrbit w).log = 0 := rfl
  have h₂ : (1 : E.filtration.realification.PolynomialOrbit w).log = 0 := rfl
  let A := VectorPolynomial.map (σ := σ)
    ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ)
  let B := VectorPolynomial.map (σ := σ)
    ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
  have hsum (a : D.filtration.realification.PolynomialOrbit w)
      (b : E.filtration.realification.PolynomialOrbit w) :
      (pairOrbit D E a b).log = A a.log + B b.log := by
    let inputs (i : Bool) : (pairModels D E i).filtration.realification.PolynomialOrbit w := by
      cases i
      · exact b
      · exact a
    change (∑ i : Bool, VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) i).restrictScalars ℚ) (inputs i).log) = _
    rw [Fintype.sum_bool]
    rfl
  have hA : A (1 : D.filtration.realification.PolynomialOrbit w).log = 0 :=
    (congrArg A h₁).trans A.map_zero
  have hB : B (1 : E.filtration.realification.PolynomialOrbit w).log = 0 :=
    (congrArg B h₂).trans B.map_zero
  have hleft : (pairOrbit D E p 1).log = A p.log :=
    (hsum p 1).trans ((congrArg (A p.log + ·) hB).trans (add_zero _))
  have hright : (pairOrbit D E 1 q).log = B q.log :=
    (hsum 1 q).trans ((congrArg (· + B q.log) hA).trans (zero_add _))
  exact (hsum p q).trans (congrArg₂ (· + ·) hleft.symm hright.symm)

/-- The symbol-coordinate splitting is obtained by applying the linear
symbol map to the two product axes. -/
theorem native_pairOrbitSymbol_coord_add_axes
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (F₂).layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    (pairOrbitSymbol D E p q b ω hF).coord =
      (pairOrbitSymbol D E p 1 b ω hF).coord + (pairOrbitSymbol D E 1 q b ω hF).coord := by
  change (F₂).realSymbolOfPolynomial b ω hF w (pairOrbit D E p q).log =
    (F₂).realSymbolOfPolynomial b ω hF w (pairOrbit D E p 1).log +
      (F₂).realSymbolOfPolynomial b ω hF w (pairOrbit D E 1 q).log
  rw [native_pairOrbit_log_add_axes, map_add]

end PairAxes

section NativeRows

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
    (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)

/-- Place the first copy in a positive slot and the conjugate copy in a
negative slot of the upstream four-coordinate projection. -/
def nativeTypeIIFourSlotMap : PairAlgebra L L →ₗ⁅ℚ⁆ (Fin 4 → L) :=
  liePiMap (M := fun _ : Fin 4 => L) (fun j =>
    if j = 0 then liePiEval (R := ℚ) true else if j = 2 then liePiEval (R := ℚ) false else 0)

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D D)))
local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))

/-- The signed four-slot frequency is the native pair frequency with
the conjugate sign in the second component. -/
theorem nativeTypeIIFourSlotMap_frequency (η : L →ₗ[ℚ] ℚ) (x : PairAlgebra L L) :
    pairFrequency η (-η) x = η (Φ x 0) + η (Φ x 1) - η (Φ x 2) - η (Φ x 3) := by
  have h0 : Φ x 0 = x true := rfl
  have h1 : Φ x 1 = 0 := rfl
  have h2 : Φ x 2 = x false := rfl
  have h3 : Φ x 3 = 0 := rfl
  simp only [pairFrequency_apply, h0, h1, h2, h3, map_zero, sub_eq_add_neg, neg_zero, add_zero]
  rfl

theorem nativeTypeIIFourSlotMap_mem_layer (d : ℕ) (x : PairAlgebra L L)
    (hx : x ∈ (F₂).layer d) (i : Fin 4) : Φ x i ∈ R.filtration.layer d 1 := by
  change x ∈ (NilpotentLieFiltration.pi (fun j => (pairModels D D j).filtration)).layer d at hx
  rw [NilpotentLieFiltration.mem_pi_layer] at hx
  rw [← R.filtration.rank_zero_eq_one]
  change Φ x i ∈ R.filtration.associatedDegree.layer d
  rw [R.associated]
  by_cases hi : i = 0
  · subst i
    change x true ∈ D.filtration.layer d
    exact hx true
  by_cases hi₂ : i = 2
  · subst i
    change x false ∈ D.filtration.layer d
    exact hx false
  · simp [nativeTypeIIFourSlotMap, hi, hi₂]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {ι : Type*}

local notation "hΦ" => (nativeTypeIIFourSlotMap_mem_layer D R)

/-- Horizontal row evaluations on the actual Type II orbit symbols
separate into the two undilated coordinate coefficients. Conjugation
changes the observable and leaves the polynomial orbit intact. -/
theorem native_typeII_dilation_projected_row_eq
    (T : D.Niltest (fun _ : Unit => 1)) (d e k : ℕ)
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ j, (F₂).layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (row : (Fin 4 → R.filtration.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () k))) →ₗ[ℚ] ℚ) :
    let f := projectedHorizontalRow R.filtration F₂ Φ hΦ (fun _ => 1) (Finsupp.single () k) row
    let V := T.scalarAffinePullback (d : ℚ) (fun _ => 0)
    let W := (T.scalarAffinePullback (e : ℚ) (fun _ => 0)).conjugate
    f (pairOrbitSymbol D D V.orbit W.orbit b ω hF).coord =
      f (pairOrbitSymbol D D T.orbit 1 b ω hF).coord * (d : ℝ) ^ k +
        f (pairOrbitSymbol D D 1 T.orbit b ω hF).coord * (e : ℝ) ^ k := by
  intro f V W
  let w : Unit → ℕ := fun _ => 1
  let α := Finsupp.single () k
  have hweight : Finsupp.weight w α = k := by
    simp only [α, Finsupp.weight_single, w, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hleft : pairOrbitSymbol D D V.orbit 1 b ω hF =
      (F₂).realPolynomialSymbolDilationHom w (d : ℚ) (pairOrbitSymbol D D T.orbit 1 b ω hF) := by
    simpa only [V, w, Niltest.scalarAffinePullback, Niltest.substitute, map_one] using
      pairOrbitSymbol_scalarAffine_substitute D D T.orbit 1 b ω hF
      (d : ℚ) (fun _ : Unit => 0)
  have hright : pairOrbitSymbol D D 1 W.orbit b ω hF =
      (F₂).realPolynomialSymbolDilationHom w (e : ℚ) (pairOrbitSymbol D D 1 T.orbit b ω hF) := by
    simpa only [W, w, Niltest.conjugate, Niltest.scalarAffinePullback, Niltest.substitute, map_one] using
      pairOrbitSymbol_scalarAffine_substitute D D 1 T.orbit b ω hF
      (e : ℚ) (fun _ : Unit => 0)
  rw [native_pairOrbitSymbol_coord_add_axes, map_add, hleft, hright,
    realPolynomialSymbolDilationHom_coord, realPolynomialSymbolDilationHom_coord]
  change projectedHorizontalRow R.filtration F₂ Φ hΦ w α row
      ((F₂).realPolynomialSymbolDilation w (d : ℚ) (pairOrbitSymbol D D T.orbit 1 b ω hF).coord) +
    projectedHorizontalRow R.filtration F₂ Φ hΦ w α row
      ((F₂).realPolynomialSymbolDilation w (e : ℚ) (pairOrbitSymbol D D 1 T.orbit b ω hF).coord) = _
  rw [projectedHorizontalRow_dilation, projectedHorizontalRow_dilation]
  simp only [hweight, Rat.cast_natCast, f]
  ring

/-- For one fixed rank-sensitive annihilator row, the actual Type II
factorization gives the separated near-integer constraint at degree `k`. -/
theorem native_typeII_projected_row_near_integer [Fintype ι]
    (hs : 1 ≤ s) (T : D.Niltest (fun _ : Unit => 1)) (d e k : ℕ)
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ j, (F₂).layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {H : ℝ} (hH : 0 < H) (p : ℝ) (l : ℕ) (U : LieSubalgebra ℚ (F₂).AssociatedGraded)
    (row : (Fin 4 → R.filtration.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () k))) →ₗ[ℚ] ℚ)
    (hrow : (R.filtration.layerHorizontalImage ((F₂).gradedRefiltrationLayer U) Φ
      (fun j x hx => hΦ j x ((F₂).gradedRefiltrationLayer_le U j hx))
        (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () k))) ≤ LinearMap.ker row)
    (q : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hinteger : ∀ z : SymbolBasisIndex (fun _ : Unit => 1) ω, ∃ a : ℤ,
      (q : ℚ) * row (R.filtration.projectedHorizontalSymbolCoefficient F₂ Φ hΦ (fun _ => 1)
        (Finsupp.single () k) ((F₂).polynomialSymbolBasis b ω hF (fun _ => 1) z)) =
          (a : ℚ) ∧ |(a : ℝ)| ≤ A) :
    let V := T.scalarAffinePullback (d : ℚ) (fun _ => 0)
    let W := (T.scalarAffinePullback (e : ℚ) (fun _ => 0)).conjugate
    let Z := pairOrbitSymbol D D V.orbit W.orbit b ω hF
    (F₂).SymbolFactorizationIn b ω hF (fun _ => H) Z p l U →
      let f := projectedHorizontalRow R.filtration F₂ Φ hΦ (fun _ => 1) (Finsupp.single () k) row
      ∃ a : ℤ, |((↑(q * l) : ℝ) * f (pairOrbitSymbol D D T.orbit 1 b ω hF).coord) * (d : ℝ) ^ k +
        ((↑(q * l) : ℝ) * f (pairOrbitSymbol D D 1 T.orbit b ω hF).coord) * (e : ℝ) ^ k -
          (a : ℝ)| ≤ (l : ℝ) * (↑(Fintype.card ι * (s + 1) * 2 ^ s) : ℝ) * A * Real.exp p / H ^ k := by
  intro V W Z hfactor f
  have hsep : f Z.coord =
    f (pairOrbitSymbol D D T.orbit 1 b ω hF).coord * (d : ℝ) ^ k +
      f (pairOrbitSymbol D D 1 T.orbit b ω hF).coord * (e : ℝ) ^ k :=
    native_typeII_dilation_projected_row_eq D R T d e k b ω hF row
  obtain ⟨a, ha⟩ := projected_horizontal_row_near_integer R.filtration F₂ Φ hΦ hs b ω hF
    (fun _ : Unit => H) (fun _ => hH) Z p l U hfactor (Finsupp.single () k) row hrow q hA hinteger
  have hmul : (↑(q * l) : ℝ) * f Z.coord =
    ((↑(q * l) : ℝ) * f (pairOrbitSymbol D D T.orbit 1 b ω hF).coord) * (d : ℝ) ^ k +
      ((↑(q * l) : ℝ) * f (pairOrbitSymbol D D 1 T.orbit b ω hF).coord) * (e : ℝ) ^ k := by
    rw [hsep]
    ring
  refine ⟨a, ?_⟩
  rw [← hmul]
  have hscale : monomialScale (fun _ : Unit => H) (Finsupp.single () k) = H ^ k := by
    simp [monomialScale, Finsupp.prod_single_index]
  simpa only [f, hscale, Fintype.card_unique, Nat.one_add, Nat.reduceAdd] using ha


end NativeRows

end PrimeUniformity
