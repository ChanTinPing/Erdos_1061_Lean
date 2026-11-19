import PrimeUniformity.UpstreamTypeIISymbols

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold
open scoped TensorProduct

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
    (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)
    {ι : Type*} [Fintype ι]

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D D)))
local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))
local notation "hΦ" => (nativeTypeIIFourSlotMap_mem_layer D R)

private theorem exists_typeII_integer_symbol_columns
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ k, (F₂).layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (col : SymbolBasisIndex (fun _ : Unit => 1) ω → ℚ)
    {B : ℕ} (hB : 1 ≤ B) (hheight : ∀ z, RationalHeightLE (col z) B) :
    let N := Fintype.card ι * (s + 1) * 2 ^ s
    ∃ q : ℕ, 0 < q ∧ q ≤ B ^ N ∧
      ∀ z, ∃ a : ℤ, (q : ℚ) * col z = (a : ℚ) ∧ |(a : ℝ)| ≤ (B ^ N : ℕ) := by
  classical
  intro N
  let w : Unit → ℕ := fun _ => 1
  let : Fintype (SymbolBasisIndex w ω) := symbolBasisIndexFintype w ω s
    (fun _ => Nat.zero_lt_one) ((F₂).adaptedBasis_weight_le_step b ω hF)
  have hcard : Fintype.card (SymbolBasisIndex w ω) ≤ N := by
    simpa only [N, Fintype.card_unit, Nat.reduceAdd] using
      symbolBasisIndex_card_le w ω s (fun _ => Nat.zero_lt_one)
        ((F₂).adaptedBasis_weight_le_step b ω hF)
  have hbound : B ^ Fintype.card (SymbolBasisIndex w ω) ≤ B ^ N :=
    Nat.pow_le_pow_right hB hcard
  obtain ⟨q, hq, hqB, a, ha, haB⟩ := exists_bounded_integer_array col hheight
  refine ⟨q, hq, hqB.trans hbound, fun z => ⟨a z, (ha z).symm, ?_⟩⟩
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast (haB z).trans hbound

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

/-- Shared factorizations of the native dilated pairs give simultaneous
near-integer constraints on all selected horizontal rows. The row
multipliers are fixed across the factor pairs. -/
theorem exists_typeII_projected_rows_of_common_symbol_factors
    {J : Fin s → Type*}
    (hs : 1 ≤ s) (T : D.Niltest (fun _ : Unit => 1))
    (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
    (hF : ∀ k, (F₂).layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (row : ∀ (j : Fin s), J j → (Fin 4 → R.filtration.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (j.val + 1)))) →ₗ[ℚ] ℚ)
    (U : LieSubalgebra ℚ (F₂).AssociatedGraded)
    (p : ℝ) (l : ℕ) (hl : 0 < l) (S : Finset (ℕ × ℕ)) (side : ℕ × ℕ → ℝ)
    {Y : ℝ} (hY : 0 < Y) (hside : ∀ v ∈ S, Y ≤ side v) {B : ℕ} (hB : 1 ≤ B) :
    let w : Unit → ℕ := fun _ => 1
    let α (j : Fin s) := Finsupp.single () (j.val + 1)
    (∀ v ∈ S,
      let V := T.scalarAffinePullback (v.1 : ℚ) (fun _ => 0)
      let W := (T.scalarAffinePullback (v.2 : ℚ) (fun _ => 0)).conjugate
      (F₂).SymbolFactorizationIn b ω hF (fun _ => side v)
        (pairOrbitSymbol D D V.orbit W.orbit b ω hF) p l U) →
    (∀ j i, R.filtration.layerHorizontalImage ((F₂).gradedRefiltrationLayer U) Φ
      (fun k x hx => hΦ k x ((F₂).gradedRefiltrationLayer_le U k hx))
        (Finsupp.weight w (α j)) ≤ LinearMap.ker (row j i)) →
    (∀ j i (z : SymbolBasisIndex w ω), RationalHeightLE
      (row j i (R.filtration.projectedHorizontalSymbolCoefficient F₂ Φ hΦ w (α j)
        ((F₂).polynomialSymbolBasis b ω hF w z))) B) →
    let N := Fintype.card ι * (s + 1) * 2 ^ s
    let A := B ^ N
    let H := (l : ℝ) * (N : ℝ) * (A : ℝ) * Real.exp p
    let θ (j : Fin s) (i : J j) (k : Bool) :=
      let f := projectedHorizontalRow R.filtration F₂ Φ hΦ w (α j) (row j i)
      f (pairOrbitSymbol D D (if k then T.orbit else 1)
        (if k then 1 else T.orbit) b ω hF).coord
    ∃ m : ∀ j, J j → ℕ, (∀ j i, 0 < m j i ∧ m j i ≤ A * l) ∧
      ∀ v ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * θ j i true) * (v.1 : ℝ) ^ (j.val + 1) +
          ((m j i : ℝ) * θ j i false) * (v.2 : ℝ) ^ (j.val + 1) - a| ≤ H / Y ^ (j.val + 1) := by
  intro w α hfactor hann hcolumns N A H θ
  have hclear (j : Fin s) (i : J j) := exists_typeII_integer_symbol_columns D b ω hF
    (fun z => row j i (R.filtration.projectedHorizontalSymbolCoefficient F₂ Φ hΦ w (α j)
      ((F₂).polynomialSymbolBasis b ω hF w z))) hB (hcolumns j i)
  choose q hq hqA hcol using hclear
  refine ⟨fun j i => q j i * l, fun j i => ⟨Nat.mul_pos (hq j i) hl,
    Nat.mul_le_mul_right _ (hqA j i)⟩, ?_⟩
  intro v hv j i
  obtain ⟨a, ha⟩ := native_typeII_projected_row_near_integer D R hs T v.1 v.2 (j.val + 1)
    b ω hF (hY.trans_le (hside v hv)) p l U (row j i) (hann j i) (q j i)
    (Nat.cast_nonneg A) (hcol j i) (hfactor v hv)
  refine ⟨a, ?_⟩
  have hYside : H / (side v) ^ (j.val + 1) ≤ H / Y ^ (j.val + 1) :=
    div_le_div_of_nonneg_left (by dsimp only [H]; positivity) (pow_pos hY _)
      (pow_le_pow_left₀ hY.le (hside v hv) _)
  simpa [θ, w, α, N, A, H] using ha.trans hYside

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeII_projected_rows_of_common_symbol_factors
