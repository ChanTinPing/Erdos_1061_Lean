import OAI.Combinatorics.Progressions.Estimates.ProjectedHorizontalFactorization

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

section ProjectedRows

private noncomputable def realifyProjectedRow {V : Type*} [AddCommGroup V] [Module ℚ V]
    (row : V →ₗ[ℚ] ℚ) : (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap.comp (row.baseChange ℝ)

private theorem realifyProjectedRow_tmul {V : Type*} [AddCommGroup V] [Module ℚ V]
    (row : V →ₗ[ℚ] ℚ) (a : ℝ) (x : V) :
    realifyProjectedRow row (a ⊗ₜ[ℚ] x) = a * (row x : ℝ) := by
  simp only [realifyProjectedRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, Rat.smul_def, mul_comm]

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ j, φ x j ∈ G.layer d 1)

noncomputable def projectedHorizontalRow (w : σ → ℕ) (α : σ →₀ ℕ)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ) :
    (ℝ ⊗[ℚ] F.PolynomialSymbol w) →ₗ[ℝ] ℝ :=
  (realifyProjectedRow row).comp
    ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ)

/-- After passing to the horizontal quotient, a row that annihilates the
refiltered fast image sees only the smooth and rational factors. -/
theorem exists_projected_horizontal_row_factorization
    (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF T X p l U) :
    ∃ E R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      ∀ (α : σ →₀ ℕ) (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight (fun _ => 1) α)) →ₗ[ℚ] ℚ),
        (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
          (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
            (Finsupp.weight (fun _ => 1) α)) ≤ LinearMap.ker row →
        projectedHorizontalRow G F φ hφ (fun _ => 1) α row X.coord =
          projectedHorizontalRow G F φ hφ (fun _ => 1) α row E.coord +
            projectedHorizontalRow G F φ hφ (fun _ => 1) α row R.coord := by
  obtain ⟨E, R, hE, hR, hfast⟩ := G.projectedHorizontal_factorization F φ hφ ht b ω hF T X p l U hfactor
  refine ⟨E, R, hE, hR, ?_⟩
  intro α row hrow
  let f := (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ : σ => 1) α).baseChange ℝ
  have hres : f X.coord - f E.coord - f R.coord ∈ (LinearMap.ker row).baseChange ℝ :=
    Submodule.baseChange_mono ℝ hrow (hfast α)
  have hker : (LinearMap.ker row).baseChange ℝ = LinearMap.ker (row.baseChange ℝ) := by
    let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
    exact (Module.Flat.ker_lTensor_eq ℝ ℝ row).symm
  rw [hker, LinearMap.mem_ker] at hres
  have hz : realifyProjectedRow row (f X.coord - f E.coord - f R.coord) = 0 := by
    change (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ) (row.baseChange ℝ
      (f X.coord - f E.coord - f R.coord)) = 0
    rw [hres, map_zero]
  simp only [map_sub] at hz
  change realifyProjectedRow row (f X.coord) =
    realifyProjectedRow row (f E.coord) + realifyProjectedRow row (f R.coord)
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

/-- A projected row at monomial `α` ignores symbol-basis vectors supported
on every other monomial. -/
theorem projectedHorizontalCoefficient_basis_eq_zero
    (b : Basis ι ℚ M) (ω : ι → ℕ) (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (z : SymbolBasisIndex w ω) (hz : z.val.1 ≠ α) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolBasis b ω hF w z) = 0 := by
  classical
  rw [F.polynomialSymbolBasis_apply, G.projectedHorizontalSymbolCoefficient_symbol]
  have hcoeff : coefficients (((F.adaptedMonomialBasis b ω hF w) ⟨z.val, z.property.le⟩ :
      F.adaptedLieSubalgebra w) : VectorPolynomial σ ℚ M) α = 0 := by
    rw [F.adaptedMonomialBasis_coe, coefficients_monomial]
    simp [Ne.symm hz]
  rw [show (⟨_, _⟩ : F.layer (Finsupp.weight w α)) = 0 from Subtype.ext hcoeff, map_zero]

/-- Convert a controlled horizontal factorization into a near-integer
constraint. Clearing the row's rational coefficients costs `q`, and
clearing the rational symbol grid costs `l`. Only basis coordinates at the
selected monomial contribute to the slow error. -/
theorem projected_horizontal_row_near_integer [Fintype σ] [Fintype ι]
    (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF T X p l U)
    (α : σ →₀ ℕ) (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight (fun _ => 1) α)) →ₗ[ℚ] ℚ)
    (hrow : (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
      (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
        (Finsupp.weight (fun _ => 1) α)) ≤ LinearMap.ker row)
    (q : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hinteger : ∀ z : SymbolBasisIndex (fun _ : σ => 1) ω, ∃ a : ℤ,
      (q : ℚ) * row (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α
        (F.polynomialSymbolBasis b ω hF (fun _ => 1) z)) = (a : ℚ) ∧ |(a : ℝ)| ≤ A) :
    ∃ a : ℤ, |(↑(q * l) : ℝ) *
      projectedHorizontalRow G F φ hφ (fun _ => 1) α row X.coord - (a : ℝ)| ≤
      (l : ℝ) * (↑(Fintype.card ι * (t + 1) * (Fintype.card σ + 1) ^ t) : ℝ) *
        A * Real.exp p / monomialScale T α := by
  classical
  let w : σ → ℕ := fun _ => 1
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω t (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step b ω hF)
  let B := (F.polynomialSymbolBasis b ω hF w).baseChange ℝ
  let f := projectedHorizontalRow G F φ hφ w α row
  let N := Fintype.card ι * (t + 1) * (Fintype.card σ + 1) ^ t
  have hcard : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast symbolBasisIndex_card_le w ω t (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step b ω hF)
  obtain ⟨E, R, hE, hR, hsplit⟩ := exists_projected_horizontal_row_factorization
    G F φ hφ ht b ω hF T X p l U hfactor
  change ∀ z : SymbolBasisIndex w ω, |B.repr E.coord z| ≤ Real.exp p / monomialScale T z.val.1 at hE
  choose c hc hcA using hinteger
  have hcolumn (z : SymbolBasisIndex w ω) : (q : ℝ) * f (B z) = (c z : ℝ) := by
    have hz := congrArg (fun x : ℚ => (x : ℝ)) (hc z)
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, f, B, projectedHorizontalRow,
      LinearMap.comp_apply, Basis.baseChange_apply, LinearMap.baseChange_tmul,
      realifyProjectedRow_tmul, one_mul] using hz
  have heval (x : ℝ ⊗[ℚ] F.PolynomialSymbol w) :
      (q : ℝ) * f x = ∑ z, B.repr x z * (c z : ℝ) := by
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_smul, smul_eq_mul, mul_left_comm, hcolumn]
  have hscale : 0 < monomialScale T α := monomialScale_pos T hT α
  have hslow : |(q : ℝ) * f E.coord| ≤ (N : ℝ) * (A * (Real.exp p / monomialScale T α)) := by
    rw [heval]
    calc
      _ ≤ ∑ z, |B.repr E.coord z * (c z : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z : SymbolBasisIndex w ω, A * (Real.exp p / monomialScale T α) := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : z.val.1 = α
        · rw [abs_mul, mul_comm]
          have hB := (hE z).trans_eq (congrArg (fun a => Real.exp p / monomialScale T a) hz)
          exact mul_le_mul (hcA z) hB (abs_nonneg _) hA
        · have hz0 := projectedHorizontalCoefficient_basis_eq_zero G F φ hφ b ω hF w α z hz
          have hf0 : f (B z) = 0 := by
            simp only [f, B, projectedHorizontalRow, LinearMap.comp_apply, Basis.baseChange_apply,
              LinearMap.baseChange_tmul, hz0, TensorProduct.tmul_zero, map_zero]
          have hc0 : (c z : ℝ) = 0 := (hcolumn z).symm.trans (by rw [hf0, mul_zero])
          rw [hc0, mul_zero, abs_zero]
          positivity
      _ = (Fintype.card (SymbolBasisIndex w ω) : ℝ) * (A * (Real.exp p / monomialScale T α)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  obtain ⟨v, hv⟩ := hR
  have hgrid (z : SymbolBasisIndex w ω) : (l : ℝ) * B.repr R.coord z = (v z : ℝ) :=
    (congrFun hv z).symm
  let a : ℤ := ∑ z, v z * c z
  have hrational : (l : ℝ) * ((q : ℝ) * f R.coord) = (a : ℝ) := by
    rw [heval, Finset.mul_sum]
    simp only [a, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [← mul_assoc, hgrid]
  refine ⟨a, ?_⟩
  have heq : (↑(q * l) : ℝ) * f X.coord - (a : ℝ) = (l : ℝ) * ((q : ℝ) * f E.coord) := by
    rw [Nat.cast_mul, ← hrational, show f X.coord = f E.coord + f R.coord from hsplit α row hrow]
    ring
  rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
  exact (mul_le_mul_of_nonneg_left hslow (Nat.cast_nonneg l)).trans_eq (by ring)


/-- Homogeneous dilation multiplies the rank-one coefficient at `α`
by the corresponding scalar power. -/
theorem projectedHorizontalCoefficient_dilation
    (w : σ → ℕ) (d : ℚ) (α : σ →₀ ℕ) (X : F.PolynomialSymbol w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolDilation w d X) =
      d ^ Finsupp.weight w α • G.projectedHorizontalSymbolCoefficient F φ hφ w α X := by
  obtain ⟨P, rfl⟩ := F.polynomialSymbolMap_surjective w X
  rw [F.polynomialSymbolDilation_map, G.projectedHorizontalSymbolCoefficient_symbol,
    G.projectedHorizontalSymbolCoefficient_symbol, ← map_smul]
  congr 1
  apply Subtype.ext
  change coefficients (F.adaptedWeightedDilation w d P : VectorPolynomial σ ℚ M) α =
    d ^ Finsupp.weight w α • coefficients (P : VectorPolynomial σ ℚ M) α
  rw [F.adaptedWeightedDilation_coe, coefficients_weightedDilation]

theorem projectedHorizontalRow_dilation (w : σ → ℕ) (d : ℚ) (α : σ →₀ ℕ)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w) :
    projectedHorizontalRow G F φ hφ w α row (F.realPolynomialSymbolDilation w d x) =
      (d : ℝ) ^ Finsupp.weight w α * projectedHorizontalRow G F φ hφ w α row x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [F.realPolynomialSymbolDilation_tmul, projectedHorizontalRow, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, projectedHorizontalCoefficient_dilation,
      realifyProjectedRow_tmul, map_smul, smul_eq_mul, Rat.cast_mul, Rat.cast_pow]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- When the two components of a pair are represented by their inclusions
into the product, a row evaluation on the dilated pair separates exactly
into two monomial powers. The additivity used here is that of the proven
rank-one projection homomorphism. -/
theorem projectedHorizontalRow_pair_dilation
    (ht : 1 ≤ t) (w : σ → ℕ) (d e : ℚ) (α : σ →₀ ℕ)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ] ℚ)
    (X Y : F.RealPolynomialSymbolGroup w) :
    projectedHorizontalRow G F φ hφ w α row
        (F.realPolynomialSymbolDilationHom w d X * F.realPolynomialSymbolDilationHom w e Y).coord =
      projectedHorizontalRow G F φ hφ w α row X.coord * (d : ℝ) ^ Finsupp.weight w α +
        projectedHorizontalRow G F φ hφ w α row Y.coord * (e : ℝ) ^ Finsupp.weight w α := by
  let V := F.realPolynomialSymbolDilationHom w d X
  let W := F.realPolynomialSymbolDilationHom w e Y
  have hadd := congrArg Multiplicative.toAdd
    (map_mul (G.realProjectedHorizontalSymbolHom F φ hφ ht w α) V W)
  change (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ (V * W).coord =
    (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ V.coord +
    (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ W.coord at hadd
  change realifyProjectedRow row ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
      (V * W).coord) = _
  rw [hadd, map_add]
  change projectedHorizontalRow G F φ hφ w α row (F.realPolynomialSymbolDilation w d X.coord) +
    projectedHorizontalRow G F φ hφ w α row (F.realPolynomialSymbolDilation w e Y.coord) = _
  rw [projectedHorizontalRow_dilation, projectedHorizontalRow_dilation]
  ring


/-- The coefficients supplied to two-variable dilation recovery come
from the two undilated product-axis symbols. In one integer variable,
the error scale is `T^k` and the monomial powers are `d^k` and `e^k`. -/
theorem projected_horizontal_pair_dilation_near_integer [Fintype ι]
    (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {T : ℝ} (hT : 0 < T) (d e k : ℕ)
    (X Y : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF (fun _ => T)
      (F.realPolynomialSymbolDilationHom (fun _ => 1) (d : ℚ) X *
        F.realPolynomialSymbolDilationHom (fun _ => 1) (e : ℚ) Y) p l U)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () k))) →ₗ[ℚ] ℚ)
    (hrow : (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
      (fun j x hx => hφ j x (F.gradedRefiltrationLayer_le U j hx))
        (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () k))) ≤ LinearMap.ker row)
    (q : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hinteger : ∀ z : SymbolBasisIndex (fun _ : Unit => 1) ω, ∃ a : ℤ,
      (q : ℚ) * row (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) (Finsupp.single () k)
        (F.polynomialSymbolBasis b ω hF (fun _ => 1) z)) = (a : ℚ) ∧ |(a : ℝ)| ≤ A) :
    let f := projectedHorizontalRow G F φ hφ (fun _ => 1) (Finsupp.single () k) row
    ∃ a : ℤ, |((↑(q * l) : ℝ) * f X.coord) * (d : ℝ) ^ k +
      ((↑(q * l) : ℝ) * f Y.coord) * (e : ℝ) ^ k - (a : ℝ)| ≤
      (l : ℝ) * (↑(Fintype.card ι * (t + 1) * 2 ^ t) : ℝ) * A * Real.exp p / T ^ k := by
  intro f
  let w : Unit → ℕ := fun _ => 1
  let α := Finsupp.single () k
  let Z := F.realPolynomialSymbolDilationHom w (d : ℚ) X *
    F.realPolynomialSymbolDilationHom w (e : ℚ) Y
  have hweight : Finsupp.weight w α = k := by
    simp only [α, Finsupp.weight_single, w, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hsep : f Z.coord = f X.coord * (d : ℝ) ^ k + f Y.coord * (e : ℝ) ^ k := by
    simpa only [f, Z, hweight, Rat.cast_natCast] using
      projectedHorizontalRow_pair_dilation G F φ hφ ht w (d : ℚ) (e : ℚ) α row X Y
  have hscale : monomialScale (fun _ : Unit => T) α = T ^ k := by
    simp [α, monomialScale, Finsupp.prod_single_index]
  obtain ⟨a, ha⟩ := projected_horizontal_row_near_integer G F φ hφ ht b ω hF
    (fun _ : Unit => T) (fun _ => hT) Z p l U hfactor α row hrow q hA hinteger
  refine ⟨a, ?_⟩
  have hrewrite : (↑(q * l) : ℝ) * f Z.coord =
      ((↑(q * l) : ℝ) * f X.coord) * (d : ℝ) ^ k + ((↑(q * l) : ℝ) * f Y.coord) * (e : ℝ) ^ k := by
    rw [hsep]
    ring
  rw [← hrewrite]
  simpa only [f, w, α, hscale, Fintype.card_unique, Nat.one_add, Nat.reduceAdd] using ha


end ProjectedRows

end PrimeUniformity
