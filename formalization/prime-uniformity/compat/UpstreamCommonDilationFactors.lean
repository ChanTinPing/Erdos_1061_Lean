import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

namespace PrimeUniformity

open Module OAI.Erdos3

/-- Choose one fast subalgebra and one denominator on a uniformly counted
subset of the factor indices, retaining the given witnesses for that label. -/
theorem exists_common_bounded_dilation_factors
    {A ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (S : Finset A) (hS : S.Nonempty)
    (factor : A → LieSubalgebra ℚ L → ℕ → Prop)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hdata : ∀ a ∈ S, ∃ (W : LieSubalgebra ℚ L) (l : ℕ) (u : κ → L),
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      (∀ i j, rationalLogHeight (e.repr (u i) j) ≤ p) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ factor a W l) :
    ∃ (W : LieSubalgebra ℚ L) (l : ℕ) (u : κ → L) (T : Finset A),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * (S.card : ℝ) ≤ T.card ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      (∀ i j, rationalLogHeight (e.repr (u i) j) ≤ p) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ ∀ a ∈ T, factor a W l := by
  classical
  let : Nonempty ↥S := hS.to_subtype
  choose W l u hu hh hl hlp hfactor using fun a : ↥S => hdata a.val a.property
  let outer := FiniteProbabilityWeights.uniform ↥S
  have hcard : 0 < (Fintype.card ↥S : ℝ) := by exact_mod_cast Fintype.card_pos
  have huniv : outer.mass (Finset.univ : Finset ↥S) = 1 := by
    dsimp only [outer]
    rw [FiniteProbabilityWeights.uniform_mass, Finset.card_univ, div_self hcard.ne']
  have hmass : 0 < outer.mass (Finset.univ : Finset ↥S) := by rw [huniv]; exact one_pos
  let f := Fintype.equivFin κ
  have hW (a : ↥S) (_ : a ∈ Finset.univ) :
      ∃ v : Fin (Fintype.card κ) → L, Submodule.span ℚ (Set.range v) = (W a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p := by
    have hrange : Set.range (fun i => u a (f.symm i)) = Set.range (u a) := by
      calc
        _ = (u a) '' Set.range f.symm := (Set.range_comp (u a) f.symm)
        _ = _ := by rw [f.symm.surjective.range_eq, Set.image_univ]
    exact ⟨fun i => u a (f.symm i), by rw [hrange, hu a], fun i j => hh a (f.symm i) j⟩
  obtain ⟨a₀, _, R, _, ha₀, hsame, hlarge⟩ :=
    exists_weighted_common_fast_subalgebra_and_denominator e outer Finset.univ hmass W l
      (Fintype.card κ) hp hm hd hW (fun a _ => ⟨hl a, hlp a⟩)
  let inclusion : ↥S ↪ A := ⟨Subtype.val, Subtype.val_injective⟩
  let T := R.map inclusion
  have hsub : T ⊆ S := by
    intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    exact x.property
  have hT : T.Nonempty := ⟨a₀.val, Finset.mem_map.mpr ⟨a₀, ha₀, rfl⟩⟩
  have hretained : Real.exp (-((p + 2) ^ 5 + p)) * (S.card : ℝ) ≤ T.card := by
    rw [huniv, mul_one] at hlarge
    change _ ≤ (FiniteProbabilityWeights.uniform ↥S).mass R at hlarge
    rw [FiniteProbabilityWeights.uniform_mass] at hlarge
    simpa only [Fintype.card_coe, T, Finset.card_map] using (le_div_iff₀ hcard).mp hlarge
  refine ⟨W a₀, l a₀, u a₀, T, hsub, hT, hretained, hu a₀, hh a₀, hl a₀, hlp a₀, ?_⟩
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
  change factor x.val (W a₀) (l a₀)
  simpa only [(hsame x hx).1, (hsame x hx).2] using hfactor x

/-- Freeze the fast subalgebra and denominator for symbol factorizations on a
single supplied adapted basis, allowing the scale and frequency to vary with
the factor. -/
theorem exists_common_controlled_dilation_factors
    {A σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (S : Finset A) (hS : S.Nonempty)
    (η : A → L →ₗ[ℚ] ℚ) (side : A → σ → ℝ)
    (X : A → F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hX : ∀ a ∈ S, F.ControlledSymbolFactorization b ω hF (η a) (side a) (X a) p) :
    ∃ (W : LieSubalgebra ℚ F.AssociatedGraded) (l : ℕ)
        (u : ι → F.AssociatedGraded) (T : Finset A),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * (S.card : ℝ) ≤ T.card ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      ∀ a ∈ T,
        (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF (η a) x = 0) ∧
        F.SymbolFactorizationIn b ω hF (side a) (X a) p l W := by
  let e := F.associatedGradedBasis b ω hF
  let factor (a : A) (W : LieSubalgebra ℚ F.AssociatedGraded) (l : ℕ) :=
    BasisGradedSubmodule e ω W.toSubmodule ∧
      (∀ x ∈ W, basisGradeProjection e ω s x = x → F.gradedFrequency b ω hF (η a) x = 0) ∧
      F.SymbolFactorizationIn b ω hF (side a) (X a) p l W
  have hdata (a : A) (ha : a ∈ S) :
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded) (l : ℕ) (u : ι → F.AssociatedGraded),
        Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
        (∀ i j, rationalLogHeight (e.repr (u i) j) ≤ p) ∧
        0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ factor a W l := by
    obtain ⟨l, W, u, hl, hlp, hu, hgrade, hh, hη, hfac⟩ :=
      NilpotentLieFiltration.ControlledSymbolFactorization.exists_in F b ω hF (hX a ha)
    exact ⟨W, l, u, hu, hh, hl, hlp, hgrade, hη, hfac⟩
  obtain ⟨W, l, u, T, hsub, hT, hretained, hu, hh, hl, hlp, hfac⟩ :=
    exists_common_bounded_dilation_factors e S hS factor hp hd hd hdata
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨W, l, u, T, hsub, ⟨a₀, ha₀⟩, hretained, hu, (hfac a₀ ha₀).1, hh, hl, hlp,
    fun a ha => (hfac a ha).2⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_common_bounded_dilation_factors
#print axioms PrimeUniformity.exists_common_controlled_dilation_factors
