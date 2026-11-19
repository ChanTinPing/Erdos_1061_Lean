import UpstreamTypeIIAxisRows
import OAI.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
import OAI.Combinatorics.Progressions.Linear.SplitPreimageSpanning

namespace PrimeUniformity

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration RationalFilteredNilmanifold

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

/-- First coordinate of the native pair, with codomain the original Lie algebra. -/
def nativeTypeIIFirstProjection : PairAlgebra L L →ₗ⁅ℚ⁆ L :=
  liePiEval (R := ℚ) (M := BoolLieFamily L L) true

/-- Second coordinate of the native pair, with codomain the original Lie algebra. -/
def nativeTypeIISecondProjection : PairAlgebra L L →ₗ⁅ℚ⁆ L :=
  liePiEval (R := ℚ) (M := BoolLieFamily L L) false

section SaturatedAxis

variable {r : ℕ} (G : DegreeRankLieFiltration L s r)
  (A : ℕ → Submodule ℚ (PairAlgebra L L))

/-- The two rank-two coordinate subspaces in the native pair. -/
def nativeTypeIIPairRankTwo (d : ℕ) : Submodule ℚ (PairAlgebra L L) :=
  ((G.layer d 2).comap nativeTypeIIFirstProjection.toLinearMap) ⊓
    ((G.layer d 2).comap nativeTypeIISecondProjection.toLinearMap)

/-- Add the discarded rank-two directions before taking the first-axis
preimage. -/
def nativeTypeIIAxisSaturatedLayer (d : ℕ) : Submodule ℚ L :=
  ((A d) ⊔ nativeTypeIIPairRankTwo G d).comap nativeTypeIIAxisLieHom.toLinearMap

theorem nativeTypeIIAxisSaturatedLayer_mem_iff (d : ℕ) (x : L) :
    x ∈ nativeTypeIIAxisSaturatedLayer G A d ↔
      ∃ z ∈ A d, nativeTypeIIFirstProjection z - x ∈ G.layer d 2 ∧
        nativeTypeIISecondProjection z ∈ G.layer d 2 := by
  change nativeTypeIIAxisLieHom x ∈ A d ⊔ nativeTypeIIPairRankTwo G d ↔ _
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨z, hz, w, hw, he⟩
    have hw' : nativeTypeIIFirstProjection w ∈ G.layer d 2 ∧
      nativeTypeIISecondProjection w ∈ G.layer d 2 := hw
    have ht := congrArg (fun p : PairAlgebra L L => nativeTypeIIFirstProjection p) he
    have hf := congrArg (fun p : PairAlgebra L L => nativeTypeIISecondProjection p) he
    change nativeTypeIIFirstProjection z + nativeTypeIIFirstProjection w = x at ht
    change nativeTypeIISecondProjection z + nativeTypeIISecondProjection w = 0 at hf
    refine ⟨z, hz, ?_, ?_⟩
    · have heq : nativeTypeIIFirstProjection z - x = -nativeTypeIIFirstProjection w := by
        rw [← ht]
        abel
      rw [heq]
      exact Submodule.neg_mem _ hw'.1
    · have hzf : nativeTypeIISecondProjection z = -nativeTypeIISecondProjection w := by
        calc
          nativeTypeIISecondProjection z =
            (nativeTypeIISecondProjection z + nativeTypeIISecondProjection w) -
              nativeTypeIISecondProjection w := by abel
          _ = -nativeTypeIISecondProjection w := by rw [hf, zero_sub]
      rw [hzf]
      exact Submodule.neg_mem _ hw'.2
  · rintro ⟨z, hz, ht, hf⟩
    let w := nativeTypeIIAxisLieHom x - z
    have hwt : nativeTypeIIFirstProjection w ∈ G.layer d 2 := by
      change x - nativeTypeIIFirstProjection z ∈ G.layer d 2
      rw [← neg_sub]
      exact Submodule.neg_mem _ ht
    have hwf : nativeTypeIISecondProjection w ∈ G.layer d 2 := by
      change 0 - nativeTypeIISecondProjection z ∈ G.layer d 2
      rw [zero_sub]
      exact Submodule.neg_mem _ hf
    refine ⟨z, hz, w, ⟨hwt, hwf⟩, ?_⟩
    dsimp only [w]
    abel

theorem nativeTypeIIAxisSaturatedLayer_rank_two_le (d : ℕ) :
    G.layer d 2 ≤ nativeTypeIIAxisSaturatedLayer G A d := by
  intro x hx
  apply (nativeTypeIIAxisSaturatedLayer_mem_iff G A d x).mpr
  refine ⟨0, Submodule.zero_mem _, ?_, Submodule.zero_mem _⟩
  change 0 - x ∈ G.layer d 2
  rw [zero_sub]
  exact Submodule.neg_mem _ hx

theorem nativeTypeIIAxisSaturatedLayer_le_rank_one
    (hA : ∀ d z, z ∈ A d → (nativeTypeIIFirstProjection z) ∈ G.layer d 1) (d : ℕ) :
    nativeTypeIIAxisSaturatedLayer G A d ≤ G.layer d 1 := by
  intro x hx
  obtain ⟨z, hz, ht, _⟩ := (nativeTypeIIAxisSaturatedLayer_mem_iff G A d x).mp hx
  have heq : x = (nativeTypeIIFirstProjection z) - ((nativeTypeIIFirstProjection z) - x) := by abel
  rw [heq]
  exact Submodule.sub_mem _ (hA d z hz) (G.rank_antitone d (by decide : 1 ≤ 2) ht)

theorem nativeTypeIIAxisSaturatedLayer_antitone
    (hA : ∀ d z, z ∈ A d → (nativeTypeIIFirstProjection z) ∈ G.layer d 1) :
    Antitone (nativeTypeIIAxisSaturatedLayer G A) :=
  antitone_nat_of_succ_le fun d =>
    (nativeTypeIIAxisSaturatedLayer_le_rank_one G A hA (d + 1)).trans
      ((G.lex_antitone (Or.inl (Nat.lt_succ_self d))).trans
        (nativeTypeIIAxisSaturatedLayer_rank_two_le G A d))

theorem nativeTypeIIAxisSaturatedLayer_lie_mem
    (hA : ∀ d z, z ∈ A d → (nativeTypeIIFirstProjection z) ∈ G.layer d 1)
    (hbr : ∀ i j z w, z ∈ A i → w ∈ A j → ⁅z, w⁆ ∈ A (i + j))
    {i j : ℕ} {x y : L} (hx : x ∈ nativeTypeIIAxisSaturatedLayer G A i)
    (hy : y ∈ nativeTypeIIAxisSaturatedLayer G A j) :
    ⁅x, y⁆ ∈ nativeTypeIIAxisSaturatedLayer G A (i + j) := by
  obtain ⟨z, hz, hzt, hzf⟩ := (nativeTypeIIAxisSaturatedLayer_mem_iff G A i x).mp hx
  obtain ⟨w, hw, hwt, hwf⟩ := (nativeTypeIIAxisSaturatedLayer_mem_iff G A j y).mp hy
  apply (nativeTypeIIAxisSaturatedLayer_mem_iff G A (i + j) ⁅x, y⁆).mpr
  refine ⟨⁅z, w⁆, hbr i j z w hz hw, ?_, ?_⟩
  · change ⁅(nativeTypeIIFirstProjection z), (nativeTypeIIFirstProjection w)⁆ - ⁅x, y⁆ ∈ G.layer (i + j) 2
    have he : ⁅(nativeTypeIIFirstProjection z), (nativeTypeIIFirstProjection w)⁆ - ⁅x, y⁆ =
        ⁅(nativeTypeIIFirstProjection z) - x, (nativeTypeIIFirstProjection w)⁆ + ⁅x, (nativeTypeIIFirstProjection w) - y⁆ := by
      rw [sub_lie, lie_sub]
      abel
    rw [he]
    have hx₁ := nativeTypeIIAxisSaturatedLayer_le_rank_one G A hA i hx
    exact Submodule.add_mem _
      (G.rank_antitone _ (by decide : 2 ≤ 2 + 1) (G.lie_mem hzt (hA j w hw)))
      (G.rank_antitone _ (by decide : 2 ≤ 1 + 2) (G.lie_mem hx₁ hwt))
  · change ⁅(nativeTypeIISecondProjection z), (nativeTypeIISecondProjection w)⁆ ∈ G.layer (i + j) 2
    exact G.rank_antitone _ (by decide : 2 ≤ 2 + 2) (G.lie_mem hzf hwf)

/-- A leading bracket of axis vectors has zero frequency. Comparing
representatives only costs the terminal rank-`(r+1)` layer. -/
theorem nativeTypeIIAxisSaturatedLayer_top_bracket_frequency
    {I : Type*} (weight : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight weight a = s) (hr : a.length = r)
    (hA : ∀ d z, z ∈ A d → (nativeTypeIIFirstProjection z) ∈ G.layer d 1 ∧ (nativeTypeIISecondProjection z) ∈ G.layer d 1)
    (hbr : ∀ i j z w, z ∈ A i → w ∈ A j → ⁅z, w⁆ ∈ A (i + j))
    (η : L →ₗ[ℚ] ℚ) (hzero : ∀ z ∈ A s, pairFrequency η (-η) z = 0)
    (x : I → L) (hx : ∀ i, x i ∈ nativeTypeIIAxisSaturatedLayer G A (weight i)) :
    η (lieTreeEval x a) = 0 := by
  choose z hz h₁ h₂ using fun i =>
    (nativeTypeIIAxisSaturatedLayer_mem_iff G A (weight i) (x i)).mp (hx i)
  have hfast (t : FreeMagma I) : lieTreeEval z t ∈ A (lieTreeWeight weight t) := by
    induction t using FreeMagma.rec with
    | of i => exact hz i
    | mul t u ht hu => exact hbr _ _ _ _ ht hu
  have htop : lieTreeEval z a ∈ A s := hd ▸ hfast a
  have hx₁ (i : I) : x i ∈ G.layer (weight i) 1 :=
    nativeTypeIIAxisSaturatedLayer_le_rank_one G A (fun d v hv => (hA d v hv).1) (weight i) (hx i)
  have hpos : lieTreeEval (fun i => nativeTypeIIFirstProjection (z i)) a = lieTreeEval x a :=
    G.top_lieTreeEval_congr _ _ weight (fun i => (hA (weight i) (z i) (hz i)).1) hx₁ h₁ a hd hr
  have hzeroTree (t : FreeMagma I) : lieTreeEval (fun _ : I => (0 : L)) t = 0 := by
    induction t using FreeMagma.rec with
    | of i => rfl
    | mul t u ht hu => simp only [lieTreeEval, ht, hu, lie_zero]
  have hneg : lieTreeEval (fun i => nativeTypeIISecondProjection (z i)) a = 0 := by
    refine (G.top_lieTreeEval_congr _ (fun _ : I => (0 : L)) weight
      (fun i => (hA (weight i) (z i) (hz i)).2) (fun _ => Submodule.zero_mem _) ?_ a hd hr).trans
      (hzeroTree a)
    intro i
    rw [sub_zero]
    exact h₂ i
  have htrue : nativeTypeIIFirstProjection (lieTreeEval z a) = lieTreeEval (fun i => nativeTypeIIFirstProjection (z i)) a :=
    (lieTreeEval_hom nativeTypeIIFirstProjection z a).symm
  have hfalse : nativeTypeIISecondProjection (lieTreeEval z a) = lieTreeEval (fun i => nativeTypeIISecondProjection (z i)) a :=
    (lieTreeEval_hom nativeTypeIISecondProjection z a).symm
  have heval : pairFrequency η (-η) (lieTreeEval z a) = η (lieTreeEval x a) + (-η) (0 : L) :=
    (pairFrequency_apply η (-η) _).trans
      (congrArg₂ (fun u v : L => η u + (-η) v) (htrue.trans hpos) (hfalse.trans hneg))
  have h : η (lieTreeEval x a) + (-η) (0 : L) = 0 := heval.symm.trans (hzero _ htop)
  rwa [map_zero, add_zero] at h

private theorem nativeTypeIIPairRankTwo_eq (d : ℕ) :
    nativeTypeIIPairRankTwo G d =
      (G.layer d 2).map nativeTypeIIAxisLieHom.toLinearMap ⊔
        (G.layer d 2).map (liePiSingle (M := BoolLieFamily L L) false).toLinearMap := by
  apply le_antisymm
  · intro x hx
    have h : (nativeTypeIIFirstProjection x) ∈ G.layer d 2 ∧ (nativeTypeIISecondProjection x) ∈ G.layer d 2 := hx
    rw [Submodule.mem_sup]
    refine ⟨nativeTypeIIAxisLieHom ((nativeTypeIIFirstProjection x)), ⟨(nativeTypeIIFirstProjection x), h.1, rfl⟩,
      liePiSingle (M := BoolLieFamily L L) false ((nativeTypeIISecondProjection x)), ⟨(nativeTypeIISecondProjection x), h.2, rfl⟩, ?_⟩
    funext i
    cases i
    · change (0 : L) + (nativeTypeIISecondProjection x) = (nativeTypeIISecondProjection x)
      exact zero_add _
    · change (nativeTypeIIFirstProjection x) + (0 : L) = (nativeTypeIIFirstProjection x)
      exact add_zero _
  · apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hx, Submodule.zero_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨Submodule.zero_mem _, hx⟩

/-- Span the paired rank-two subspace by the two native axis inclusions. -/
theorem nativeTypeIIPairRankTwo_eq_maps (d : ℕ) :
    nativeTypeIIPairRankTwo G d =
      (G.layer d 2).map nativeTypeIIAxisLieHom.toLinearMap ⊔
        (G.layer d 2).map (liePiSingle (M := BoolLieFamily L L) false).toLinearMap :=
  nativeTypeIIPairRankTwo_eq G d

/-- A bounded generating family for the paired fast layer and for the two
rank-two axes gives a bounded basis for their saturated axis preimage. -/
theorem exists_nativeTypeIIAxisSaturatedLayer_bounded_basis
    {ι κ μ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ρ] (d : ℕ)
    (e : Basis ι ℚ L) (f : Basis κ ℚ (PairAlgebra L L))
    (v : μ → PairAlgebra L L) (hv : Submodule.span ℚ (Set.range v) = A d)
    (w : ρ → L) (hw : Submodule.span ℚ (Set.range w) = G.layer d 2)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hcount : (Fintype.card (μ ⊕ ρ ⊕ ρ) : ℝ) ≤ p)
    (hvH : ∀ i j, rationalLogHeight (f.repr (v i) j) ≤ p)
    (hwTrue : ∀ i j, rationalLogHeight (f.repr (nativeTypeIIAxisLieHom (w i)) j) ≤ p)
    (hwFalse : ∀ i j, rationalLogHeight
      (f.repr (liePiSingle (M := BoolLieFamily L L) false (w i)) j) ≤ p)
    (haxis : ∀ i j, rationalLogHeight (f.repr (nativeTypeIIAxisLieHom (e i)) j) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (nativeTypeIIAxisSaturatedLayer G A d))) ℚ
        (nativeTypeIIAxisSaturatedLayer G A d),
      ∀ i j, rationalLogHeight (e.repr (b i : L) j) ≤ preimageBasisBudget p := by
  let first := (nativeTypeIIAxisLieHom (L := L)).toLinearMap
  let second : L →ₗ[ℚ] PairAlgebra L L := (liePiSingle (M := BoolLieFamily L L) false).toLinearMap
  let z : μ ⊕ ρ ⊕ ρ → PairAlgebra L L := Sum.elim v (Sum.elim (first ∘ w) (second ∘ w))
  have hmap (T : L →ₗ[ℚ] PairAlgebra L L) :
      Submodule.span ℚ (Set.range (T ∘ w)) = (G.layer d 2).map T := by
    rw [Set.range_comp, ← Submodule.map_span, hw]
  have hz : Submodule.span ℚ (Set.range z) = A d ⊔ nativeTypeIIPairRankTwo G d := by
    change Submodule.span ℚ (Set.range (Sum.elim v (Sum.elim (first ∘ w) (second ∘ w)))) = _
    rw [span_range_sumElim, span_range_sumElim, hv, hmap first, hmap second]
    exact congrArg (A d ⊔ ·) (nativeTypeIIPairRankTwo_eq G d).symm
  have hzH (i j) : rationalLogHeight (f.repr (z i) j) ≤ p := by
    rcases i with i | (i | i)
    · exact hvH i j
    · exact hwTrue i j
    · exact hwFalse i j
  have heH (i j) : rationalLogHeight (e.repr (e i) j) ≤ p :=
    rationalLogHeight_le_of_height (basis_repr_height_one e i j)
      (by simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp)
  let P (S : Submodule ℚ L) := ∃ b : Basis (Fin (finrank ℚ S)) ℚ S,
    ∀ i j, rationalLogHeight (e.repr (b i : L) j) ≤ preimageBasisBudget p
  have hS : (⊤ : Submodule ℚ L) ⊓ (A d ⊔ nativeTypeIIPairRankTwo G d).comap first =
      nativeTypeIIAxisSaturatedLayer G A d := top_inf_eq _
  exact (congrArg P hS).mp
    (exists_preimage_basis_logHeight e f ⊤ _ first e z e.span_eq hz hp hκ hι hcount heH hzH haxis)

end SaturatedAxis

end PrimeUniformity

#print axioms PrimeUniformity.nativeTypeIIAxisSaturatedLayer_mem_iff
#print axioms PrimeUniformity.nativeTypeIIAxisSaturatedLayer_antitone
#print axioms PrimeUniformity.nativeTypeIIAxisSaturatedLayer_lie_mem
#print axioms PrimeUniformity.nativeTypeIIAxisSaturatedLayer_top_bracket_frequency
#print axioms PrimeUniformity.exists_nativeTypeIIAxisSaturatedLayer_bounded_basis
#print axioms PrimeUniformity.nativeTypeIIPairRankTwo_eq_maps
