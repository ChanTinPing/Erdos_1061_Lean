import PrimeUniformity.UpstreamTypeIIProjection

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

/-- Place the Type I symbol in the first slot of the horizontal projection. -/
def typeISingleSlot : L →ₗ⁅ℚ⁆ (Fin 4 → L) :=
  liePiMap fun i => if i = 0 then LieHom.id else 0

theorem typeISingleSlot_mem_rankOne (G : DegreeRankLieFiltration L s r) :
    ∀ d x, x ∈ G.associatedDegree.layer d → ∀ i, typeISingleSlot x i ∈ G.layer d 1 := by
  intro d x hx i
  rw [G.associatedDegree_layer, G.rank_zero_eq_one] at hx
  by_cases hi : i = 0
  · simpa [typeISingleSlot, hi] using hx
  · simp [typeISingleSlot, hi]

noncomputable def typeIMonomial (j : ℕ) : Unit →₀ ℕ := Finsupp.single () j

@[simp] theorem typeIMonomial_weight (j : ℕ) :
    Finsupp.weight (fun _ : Unit => 1) (typeIMonomial j) = j := by
  simp [typeIMonomial, Finsupp.weight_single]

@[simp] theorem typeIMonomial_scale (T : ℝ) (j : ℕ) :
    monomialScale (fun _ : Unit => T) (typeIMonomial j) = T ^ j := by
  exact Finsupp.prod_single_index (a := ()) (b := j) (h := fun _ n => T ^ n) (pow_zero T)

/-- A fixed horizontal row that annihilates the projected fast layer gives the
Type I near-integer constraint for its degree `j` coefficient. The undilated
row and the cleared coefficient are independent of the dilation `d`. -/
theorem typeI_projected_row_near_integer {ι : Type*} [Fintype ι]
    (G : DegreeRankLieFiltration L s r) (hs : 1 ≤ s)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ k, G.associatedDegree.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    {T : ℝ} (hT : 0 < T)
    (X : G.associatedDegree.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (d : ℕ) (p : ℝ) (l : ℕ) (U : LieSubalgebra ℚ G.associatedDegree.AssociatedGraded)
    (hfactor : G.associatedDegree.SymbolFactorizationIn b ω hF (fun _ : Unit => T)
      (G.associatedDegree.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (d : ℚ) X) p l U)
    (j : ℕ)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial j))) →ₗ[ℚ] ℚ)
    (hrow : G.layerHorizontalImage (G.associatedDegree.gradedRefiltrationLayer U) typeISingleSlot
      (fun k x hx => typeISingleSlot_mem_rankOne G k x (G.associatedDegree.gradedRefiltrationLayer_le U k hx))
        (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial j)) ≤ LinearMap.ker row)
    (q : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hinteger : ∀ z : SymbolBasisIndex (fun _ : Unit => 1) ω, ∃ a : ℤ,
      (q : ℚ) * row (G.projectedHorizontalSymbolCoefficient G.associatedDegree typeISingleSlot
        (typeISingleSlot_mem_rankOne G) (fun _ : Unit => 1) (typeIMonomial j)
        (G.associatedDegree.polynomialSymbolBasis b ω hF (fun _ : Unit => 1) z)) = (a : ℚ) ∧ |(a : ℝ)| ≤ A) :
    ∃ a : ℤ, |((↑(q * l) : ℝ) * projectedHorizontalRow G G.associatedDegree typeISingleSlot
      (typeISingleSlot_mem_rankOne G) (fun _ : Unit => 1) (typeIMonomial j) row X.coord) * (d : ℝ) ^ j - a| ≤
      (l : ℝ) * (↑(Fintype.card ι * (s + 1) * 2 ^ s) : ℝ) * A * Real.exp p / T ^ j := by
  obtain ⟨a, ha⟩ := projected_horizontal_row_near_integer G G.associatedDegree typeISingleSlot
    (typeISingleSlot_mem_rankOne G) hs b ω hF (fun _ : Unit => T) (fun _ => hT)
    (G.associatedDegree.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (d : ℚ) X) p l U
    hfactor (typeIMonomial j) row hrow q hA hinteger
  have hdil := projectedHorizontalRow_dilation G G.associatedDegree typeISingleSlot
    (typeISingleSlot_mem_rankOne G) (fun _ : Unit => 1) (d : ℚ) (typeIMonomial j) row X.coord
  simp only [realPolynomialSymbolDilationHom_coord, hdil, Rat.cast_natCast, typeIMonomial_weight,
    typeIMonomial_scale, Fintype.card_unit, Nat.reduceAdd] at ha
  rw [mul_comm ((d : ℝ) ^ j), ← mul_assoc] at ha
  exact ⟨a, ha⟩

/-- A bounded-height row admits one bounded denominator for all its basis
columns, independent of the symbol and of the dilation. -/
theorem exists_typeI_projected_row_integer_columns {ι : Type*} [Fintype ι]
    (G : DegreeRankLieFiltration L s r) (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ k, G.associatedDegree.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (j : ℕ)
    (row : (Fin 4 → G.HigherHorizontal (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial j))) →ₗ[ℚ] ℚ) :
    let aCol (z : SymbolBasisIndex (fun _ : Unit => 1) ω) :=
      row (G.projectedHorizontalSymbolCoefficient G.associatedDegree typeISingleSlot
        (typeISingleSlot_mem_rankOne G) (fun _ : Unit => 1) (typeIMonomial j)
        (G.associatedDegree.polynomialSymbolBasis b ω hF (fun _ : Unit => 1) z))
    ∀ {H : ℕ}, 1 ≤ H → (∀ z, RationalHeightLE (aCol z) H) →
    let B := H ^ (Fintype.card ι * (s + 1) * 2 ^ s)
    ∃ q : ℕ, 0 < q ∧ q ≤ B ∧
      ∀ z, ∃ a : ℤ, (q : ℚ) * aCol z = (a : ℚ) ∧ |(a : ℝ)| ≤ (B : ℝ) := by
  classical
  intro aCol H hH hheight B
  let w : Unit → ℕ := fun _ => 1
  let : Fintype (SymbolBasisIndex w ω) := symbolBasisIndexFintype w ω s
    (fun _ => Nat.zero_lt_one) (G.associatedDegree.adaptedBasis_weight_le_step b ω hF)
  have hcard : Fintype.card (SymbolBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * 2 ^ s := by
    simpa only [Fintype.card_unit, Nat.reduceAdd] using
      symbolBasisIndex_card_le w ω s (fun _ => Nat.zero_lt_one)
        (G.associatedDegree.adaptedBasis_weight_le_step b ω hF)
  have hbound : H ^ Fintype.card (SymbolBasisIndex w ω) ≤ B := Nat.pow_le_pow_right hH hcard
  obtain ⟨q, hq, hqB, a, ha, haB⟩ := exists_bounded_integer_array aCol hheight
  refine ⟨q, hq, hqB.trans hbound, fun z => ⟨a z, (ha z).symm, ?_⟩⟩
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast (haB z).trans hbound

end PrimeUniformity

#print axioms PrimeUniformity.typeI_projected_row_near_integer
#print axioms PrimeUniformity.exists_typeI_projected_row_integer_columns
