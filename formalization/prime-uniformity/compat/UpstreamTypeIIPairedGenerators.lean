import UpstreamTypeIIAxisRowIdentity
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
import OAI.Combinatorics.Progressions.Linear.RankHorizontalRepresentatives

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold

universe u

private theorem typeII_rowAxis_native_basis_height
    {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n : ℕ} {ι : Type*} [Fintype ι]
    (D : RationalFilteredNilmanifold L s n) (b : Basis ι ℚ (PairAlgebra L L))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hPair : (pi (pairModels D D)).GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ p)
    (c : Bool) (i : Fin n) (k : ι) :
    rationalLogHeight (b.repr (nativeTypeIIRowAxis c (D.basis i)) k) ≤
      adaptedMarkedMapHeightBudget p := by
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp p := by
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp
  have hDself (i k : Fin n) : rationalLogHeight (D.basis.repr (D.basis i) k) ≤ p :=
    rationalLogHeight_le_of_height (basis_repr_height_one D.basis i k) hOne
  apply markedMap_basisChange_logHeight D (pi (pairModels D D)) D.basis b
    (nativeTypeIIRowAxis c).toLinearMap hp hD hPair hDself hb
  intro i' k'
  cases c
  · exact rationalLogHeight_le_of_height
      (productInclusion_matrix_height (pairModels D D) false i' k') hOne
  · exact rationalLogHeight_le_of_height
      (productInclusion_matrix_height (pairModels D D) true i' k') hOne

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  (F : NilpotentLieFiltration (PairAlgebra L L) s)
  (b : Basis ι ℚ (PairAlgebra L L)) (ω : ι → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ ω i}))
  (W : LieSubalgebra ℚ F.AssociatedGraded)

/-- A common budget for the paired fast-layer generators and the
coordinates of the two rank-two summands. -/
def typeIIPairedGeneratorBudget (p : ℝ) : ℝ :=
  3 * p + refiltrationCoordinateBudget p + (p + adaptedMarkedMapHeightBudget p + 2) ^ 4

/-- A logarithmic height bound for the restricted rows in the original
single-orbit basis. -/
def typeIIPairedAxisRowLogBudget (p : ℝ) : ℝ :=
  (p + adaptedMarkedMapHeightBudget p + (typeIIPairedGeneratorBudget p + 3) ^ 7 + 2) ^ 4

/-- Produce generators of the paired fast layer enlarged by both
rank-two directions in the same adapted basis as the factorization. -/
theorem exists_typeII_paired_saturated_generators
    (u : κ → F.AssociatedGraded) (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hPair : (pi (pairModels D D)).GeometryComplexityLE p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ p)
    (huH : ∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p)
    (d : Fin s) :
    ∃ m : ℕ, (m : ℝ) ≤ 3 * p ∧ ∃ v : Fin m → PairAlgebra L L,
      Submodule.span ℚ (Set.range v) =
        F.gradedRefiltrationLayer W (d.val + 1) ⊔ nativeTypeIIPairRankTwo R.filtration (d.val + 1) ∧
      ∀ i j, rationalLogHeight (b.repr (v i) j) ≤ typeIIPairedGeneratorBudget p := by
  classical
  let j := d.val + 1
  let A := F.gradedRefiltrationLayer W j
  let K := R.filtration.layer j 2
  have hOne : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hbself (i k : ι) : rationalLogHeight (b.repr (b i) k) ≤ p :=
    rationalLogHeight_le_of_height (basis_repr_height_one b i k) (by simpa only [Nat.cast_one] using hOne)
  obtain ⟨a, ha⟩ := F.exists_refiltration_bases_in_coordinates b ω hF b W u hu
    hp hι hκ huH hbself j
  obtain ⟨e, he⟩ := R.exists_rank_two_basis ⟨j, Nat.succ_lt_succ d.isLt⟩
    (Nat.succ_pos d.val) hR
  have haxis := typeII_rowAxis_native_basis_height D b hp hR.1 hPair hb
  let Q := p + adaptedMarkedMapHeightBudget p
  have hcost : 0 ≤ adaptedMarkedMapHeightBudget p := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  have hpQ : p ≤ Q := le_add_of_nonneg_right hcost
  have hQcost : adaptedMarkedMapHeightBudget p ≤ Q := le_add_of_nonneg_left hp
  have hn : (Fintype.card (Fin n) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hR.1.1
  have heH (c : Bool) (i : Fin (finrank ℚ K)) (k : ι) :
      rationalLogHeight (b.repr (nativeTypeIIRowAxis c (e i : L)) k) ≤ (Q + 2) ^ 4 :=
    linearMap_coordinate_logHeight D.basis b (nativeTypeIIRowAxis c).toLinearMap
      (hp.trans hpQ) (hn.trans hpQ) (fun i' k' => (haxis c i' k').trans hQcost)
      (e i : L) (fun i' => (he i i').trans hpQ) k
  let I := Fin (finrank ℚ A) ⊕ Fin (finrank ℚ K) ⊕ Fin (finrank ℚ K)
  let aVec (i : Fin (finrank ℚ A)) : PairAlgebra L L := a i
  let eVec (i : Fin (finrank ℚ K)) : L := e i
  let first := (nativeTypeIIRowAxis (L := L) true).toLinearMap
  let second := (nativeTypeIIRowAxis (L := L) false).toLinearMap
  let v₀ : I → PairAlgebra L L := Sum.elim aVec (Sum.elim (first ∘ eVec) (second ∘ eVec))
  have hspan (T : L →ₗ[ℚ] PairAlgebra L L) :
      Submodule.span ℚ (Set.range (T ∘ eVec)) = K.map T := by
    rw [Set.range_comp, ← Submodule.map_span]
    exact congrArg (Submodule.map T) (span_submodule_basis K e)
  have hv₀ : Submodule.span ℚ (Set.range v₀) = A ⊔ nativeTypeIIPairRankTwo R.filtration j := by
    change Submodule.span ℚ (Set.range (Sum.elim aVec (Sum.elim (first ∘ eVec) (second ∘ eVec)))) = _
    rw [span_range_sumElim, span_range_sumElim, hspan first, hspan second]
    rw [show Submodule.span ℚ (Set.range aVec) = A from span_submodule_basis A a]
    exact congrArg (A ⊔ ·) (nativeTypeIIPairRankTwo_eq_maps R.filtration j).symm
  have hv₀H (i : I) (k : ι) : rationalLogHeight (b.repr (v₀ i) k) ≤ typeIIPairedGeneratorBudget p := by
    have hC := refiltrationCoordinateBudget_nonneg hp
    have hQ4 : 0 ≤ (Q + 2) ^ 4 := by positivity
    rcases i with i | (i | i)
    · exact (ha i k).trans (by dsimp [typeIIPairedGeneratorBudget]; dsimp [Q] at hQ4; linarith)
    · exact (heH true i k).trans (by dsimp [Q, typeIIPairedGeneratorBudget]; linarith)
    · exact (heH false i k).trans (by dsimp [Q, typeIIPairedGeneratorBudget]; linarith)
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ (PairAlgebra L L) := b.finiteDimensional_of_finite
  have hdimA : (finrank ℚ A : ℝ) ≤ p := by
    have hm : finrank ℚ A ≤ Fintype.card ι :=
      (Submodule.finrank_le A).trans_eq (finrank_eq_card_basis b)
    exact (Nat.cast_le.mpr hm).trans hι
  have hdimK : (finrank ℚ K : ℝ) ≤ p := by
    have hm := (Submodule.finrank_le K).trans_eq (finrank_eq_card_basis D.basis)
    exact (Nat.cast_le.mpr hm).trans hn
  have hdimI : (Fintype.card I : ℝ) ≤ 3 * p := by
    dsimp only [I]
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    linarith
  let f := Fintype.equivFin I
  let v : Fin (Fintype.card I) → PairAlgebra L L := v₀ ∘ f.symm
  have hrange : Set.range v = Set.range v₀ := by
    change Set.range (v₀ ∘ f.symm) = _
    rw [Set.range_comp, f.symm.surjective.range_eq, Set.image_univ]
  exact ⟨Fintype.card I, hdimI, v, by rw [hrange]; exact hv₀, fun i k => hv₀H (f.symm i) k⟩

/-- The paired generators also give bounded bases of the saturated
single-orbit layers in the native basis. -/
theorem exists_typeII_native_bounded_saturated_bases
    (u : κ → F.AssociatedGraded) (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hPair : (pi (pairModels D D)).GeometryComplexityLE p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ p)
    (huH : ∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p)
    (d : Fin s) :
    let S := nativeTypeIIAxisSaturatedLayer R.filtration (F.gradedRefiltrationLayer W) (d.val + 1)
    ∃ e : Basis (Fin (finrank ℚ S)) ℚ S,
      ∀ i k, rationalLogHeight (D.basis.repr (e i : L) k) ≤
        preimageBasisBudget (typeIIPairedGeneratorBudget p + p + adaptedMarkedMapHeightBudget p) := by
  intro S
  obtain ⟨m, hm, v, hv, hvH⟩ :=
    exists_typeII_paired_saturated_generators D R F b ω hF W u hu hp hR hPair hι hκ hb huH d
  let Q := typeIIPairedGeneratorBudget p
  let P := Q + p + adaptedMarkedMapHeightBudget p
  have hC := refiltrationCoordinateBudget_nonneg hp
  have hPow : 0 ≤ (p + adaptedMarkedMapHeightBudget p + 2) ^ 4 := by positivity
  have hAxis : 0 ≤ adaptedMarkedMapHeightBudget p := by unfold adaptedMarkedMapHeightBudget; positivity
  have hQ : 3 * p ≤ Q := by dsimp only [Q, typeIIPairedGeneratorBudget]; linarith
  have hpP : p ≤ P := by dsimp only [P]; linarith
  have hQP : Q ≤ P := by dsimp only [P]; linarith
  have hAxisP : adaptedMarkedMapHeightBudget p ≤ P := by dsimp only [P]; linarith
  have hsource : (Fintype.card (Fin n) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using hR.1.1.trans hpP
  have htarget : (Fintype.card (Fin m) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using (hm.trans hQ).trans hQP
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp P := by
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (hp.trans hpP)
  have hself (i j : Fin n) : rationalLogHeight (D.basis.repr (D.basis i) j) ≤ P :=
    rationalLogHeight_le_of_height (basis_repr_height_one D.basis i j) hOne
  let T := (nativeTypeIIAxisLieHom (L := L)).toLinearMap
  let K := F.gradedRefiltrationLayer W (d.val + 1) ⊔ nativeTypeIIPairRankTwo R.filtration (d.val + 1)
  let bounded (U : Submodule ℚ L) := ∃ e : Basis (Fin (finrank ℚ U)) ℚ U,
    ∀ i k, rationalLogHeight (D.basis.repr (e i : L) k) ≤ preimageBasisBudget P
  have hS : (⊤ : Submodule ℚ L) ⊓ K.comap T = S := top_inf_eq _
  exact (congrArg bounded hS).mp
    (exists_preimage_basis_logHeight D.basis b ⊤ K T D.basis v D.basis.span_eq hv
      (hp.trans hpP) (hι.trans hpP) hsource htarget hself (fun i k => (hvH i k).trans hQP)
      (fun i k => (typeII_rowAxis_native_basis_height D b hp hR.1 hPair hb true i k).trans hAxisP))

local notation "Φ" => (nativeTypeIIFourSlotMap (L := L))

/-- Choose all the bounded paired rows in one common fast algebra. Their
true-axis pullbacks have exactly the saturated kernels. -/
theorem exists_typeII_bounded_paired_rows_from_common_fast
    (hΦ : ∀ j x, x ∈ F.layer j → ∀ i, Φ x i ∈ R.filtration.layer j 1)
    (u : κ → F.AssociatedGraded) (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hPair : (pi (pairModels D D)).GeometryComplexityLE p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (b i) j) ≤ p)
    (huH : ∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) :
    let w : Unit → ℕ := fun _ => 1
    let α (d : Fin s) := Finsupp.single () (d.val + 1)
    let A := F.gradedRefiltrationLayer W
    ∃ B : ℕ, 1 ≤ B ∧ (B : ℝ) ≤ Real.exp ((typeIIPairedGeneratorBudget p + 3) ^ 7 + 1) ∧
    ∀ d : Fin s, ∃ m : ℕ, m ≤ Fintype.card ι ∧
    ∃ row : Fin m → (Fin 4 → R.filtration.HigherHorizontal (Finsupp.weight w (α d))) →ₗ[ℚ] ℚ,
    ∃ ξ : PairAlgebra L L →ₗ[ℚ] (Fin m → ℚ),
      (∀ i, R.filtration.layerHorizontalImage A Φ
        (fun j x hx => hΦ j x (F.gradedRefiltrationLayer_le W j hx))
          (Finsupp.weight w (α d)) ≤ LinearMap.ker (row i)) ∧
      (∀ i (z : SymbolBasisIndex w ω), RationalHeightLE
        (row i (R.filtration.projectedHorizontalSymbolCoefficient F Φ hΦ w (α d)
          (F.polynomialSymbolBasis b ω hF w z))) B) ∧
      LinearMap.ker ξ = A (d.val + 1) ⊔ nativeTypeIIPairRankTwo R.filtration (d.val + 1) ∧
      LinearMap.ker (ξ.comp nativeTypeIIAxisLieHom.toLinearMap) =
        nativeTypeIIAxisSaturatedLayer R.filtration A (d.val + 1) ∧
      (∀ k i, RationalHeightLE (ξ (b k) i) B) ∧
      (∀ k i, rationalLogHeight (ξ (nativeTypeIIAxisLieHom (D.basis k)) i) ≤
        typeIIPairedAxisRowLogBudget p) ∧
      ∀ (x : F.layer (Finsupp.weight w (α d))) i,
        row i (R.filtration.layerHorizontalMap F.layer Φ hΦ (Finsupp.weight w (α d)) x) =
          ξ x.val i := by
  intro w α A
  let Q := typeIIPairedGeneratorBudget p
  have hC := refiltrationCoordinateBudget_nonneg hp
  have hQ : 0 ≤ Q := by dsimp [Q, typeIIPairedGeneratorBudget]; positivity
  have hQ' : 3 * p ≤ Q := by
    dsimp only [Q, typeIIPairedGeneratorBudget]
    have hAxis : 0 ≤ (p + adaptedMarkedMapHeightBudget p + 2) ^ 4 := by positivity
    linarith
  let B := ⌈Real.exp ((Q + 3) ^ 7)⌉₊
  refine ⟨B, one_le_ceil_exp _, ceil_exp_le_exp_add_one (by positivity), ?_⟩
  intro d
  obtain ⟨m, hm, v, hv, hvH⟩ :=
    exists_typeII_paired_saturated_generators D R F b ω hF W u hu hp hR hPair hι hκ hb huH d
  have hw : Finsupp.weight w (α d) = d.val + 1 := by
    simp only [w, α, Finsupp.weight_single, nsmul_eq_mul, Nat.cast_id, mul_one]
  obtain ⟨B', _, hB', k, hk, row, ξ, hann, hcol, hker, haxis, hh, hrow⟩ :=
    exists_typeII_bounded_horizontal_rows_with_coordinates R.filtration F hΦ A
      (F.gradedRefiltrationLayer_le W) b ω hF w (α d) v (by simpa only [hw] using hv)
      (one_le_ceil_exp Q) (fun i k => rationalHeightLE_ceil_exp (hvH i k))
      (by linarith : 0 ≤ Q + 1)
      (by simpa only [Fintype.card_fin] using (hm.trans hQ').trans (le_add_of_nonneg_right zero_le_one))
      (ceil_exp_le_exp_add_one hQ)
  have hBBR : (B' : ℝ) ≤ (B : ℝ) := by
    apply hB'.trans
    have h := Nat.le_ceil (Real.exp ((Q + 3) ^ 7))
    simpa only [show Q + 1 + 2 = Q + 3 by ring] using h
  have hBB : B' ≤ B := by exact_mod_cast hBBR
  let P := p + adaptedMarkedMapHeightBudget p + (Q + 3) ^ 7
  have hAxis : 0 ≤ adaptedMarkedMapHeightBudget p := by unfold adaptedMarkedMapHeightBudget; positivity
  have hPower : 0 ≤ (Q + 3) ^ 7 := by positivity
  have hpP : p ≤ P := by dsimp only [P]; linarith
  have hAxisP : adaptedMarkedMapHeightBudget p ≤ P := by dsimp only [P]; linarith
  have hPowerP : (Q + 3) ^ 7 ≤ P := by dsimp only [P]; linarith
  have hB'P : (B' : ℝ) ≤ Real.exp P := by
    apply hB'.trans
    rw [show Q + 1 + 2 = Q + 3 by ring]
    exact Real.exp_le_exp.mpr hPowerP
  have hξ (a : ι) (i : Fin k) :
      rationalLogHeight ((Pi.basisFun ℚ (Fin k)).repr (ξ (b a)) i) ≤ P := by
    rw [Pi.basisFun_repr]
    exact rationalLogHeight_le_of_height (hh a i) hB'P
  have hη (a : Fin n) (i : Fin k) :
      rationalLogHeight (ξ (nativeTypeIIAxisLieHom (D.basis a)) i) ≤ typeIIPairedAxisRowLogBudget p := by
    have h := linearMap_coordinate_logHeight b (Pi.basisFun ℚ (Fin k)) ξ
      (hp.trans hpP) (hι.trans hpP) hξ (nativeTypeIIAxisLieHom (D.basis a))
      (fun j => (typeII_rowAxis_native_basis_height D b hp hR.1 hPair hb true a j).trans hAxisP) i
    simpa only [Pi.basisFun_repr, P, Q, typeIIPairedAxisRowLogBudget] using h
  refine ⟨k, hk, row, ξ, hann, fun i z => (hcol i z).mono hBB, ?_, ?_,
    fun i k => (hh i k).mono hBB, hη, hrow⟩
  · simpa only [hw] using hker
  · simpa only [hw] using haxis

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeII_paired_saturated_generators
#print axioms PrimeUniformity.exists_typeII_native_bounded_saturated_bases
#print axioms PrimeUniformity.exists_typeII_bounded_paired_rows_from_common_fast
