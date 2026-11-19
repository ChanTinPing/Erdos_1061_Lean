import UpstreamCommonDilationFactors
import OAI.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization

namespace PrimeUniformity

open Module OAI.Erdos3

/-- Bounded adapted basis coordinates and bounded filtration weights determine
a finite label. A single label retains the dependent witnesses on a large
subset of the original factor indices. -/
theorem exists_common_bounded_adapted_basis
    {A ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis κ ℚ L) (S : Finset A) (hS : S.Nonempty)
    (witness : (b : Basis ι ℚ L) → (ω : ι → ℕ) →
      (∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) → A → Prop)
    {B : ℝ} (hB : 0 ≤ B) (hs : (s : ℝ) ≤ Real.exp B)
    (hdata : ∀ a ∈ S, ∃ (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})),
      (∀ i j, rationalLogHeight (e.repr (b i) j) ≤ B) ∧ witness b ω hF a) :
    ∃ (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) (T : Finset A),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-(3 * (Fintype.card ι : ℝ) * (Fintype.card κ + 1) * (B + 2))) * S.card ≤
        (T.card : ℝ) ∧
      (∀ i j, rationalLogHeight (e.repr (b i) j) ≤ B) ∧ ∀ a ∈ T, witness b ω hF a := by
  classical
  have transport {b₁ b₂ : Basis ι ℚ L} {ω₁ ω₂ : ι → ℕ}
      {h₁ : ∀ k, F.layer k = Submodule.span ℚ (b₁ '' {i | k ≤ ω₁ i})}
      {h₂ : ∀ k, F.layer k = Submodule.span ℚ (b₂ '' {i | k ≤ ω₂ i})}
      {a : A} (hb : b₁ = b₂) (hω : ω₁ = ω₂) (ha : witness b₁ ω₁ h₁ a) :
      witness b₂ ω₂ h₂ a := by
    subst b₂
    subst ω₂
    exact ha
  choose b ω hF hh hW using fun a : ↥S => hdata a.val a.property
  let H := ⌈Real.exp B⌉₊
  let label (a : ↥S) (z : ι × Option κ) : ℚ :=
    match z.2 with
    | none => ω a z.1
    | some j => e.repr (b a z.1) j
  let labels : Set (ι × Option κ → ℚ) := {c | ∀ z, RationalHeightLE (c z) H}
  have hH : s ≤ H := by
    exact_mod_cast hs.trans (Nat.le_ceil (Real.exp B))
  have hHone : 1 ≤ H := one_le_ceil_exp B
  have hlabel (a : ↥S) (_ : a ∈ (Finset.univ : Finset ↥S)) : label a ∈ labels := by
    intro z
    obtain ⟨i, j⟩ := z
    cases j with
    | none =>
      change RationalHeightLE (ω a i : ℚ) H
      simpa only [RationalHeightLE, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast] using
        And.intro ((F.adaptedBasis_weight_le_step (b a) (ω a) (hF a) i).trans hH) hHone
    | some j =>
      exact rationalHeightLE_ceil_exp (hh a i j)
  obtain ⟨hfinite, hcard⟩ := finite_card_bounded_height_arrays labels H (fun _ hc => hc)
  have hcount : (labels.ncard : ℝ) ≤
      Real.exp (3 * (Fintype.card ι : ℝ) * (Fintype.card κ + 1) * (B + 2)) := by
    have h := (Nat.cast_le.mpr hcard).trans
      (rational_log_height_count_exp_bound (Fintype.card (ι × Option κ)) hB)
    simpa only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      mul_assoc] using h
  let : Nonempty ↥S := hS.to_subtype
  obtain ⟨r, _, U, _, hU, hlabel_eq, hlarge⟩ :=
    exists_exponential_constant_fiber (Finset.univ : Finset ↥S) Finset.univ_nonempty
      label labels hfinite hlabel hcount
  obtain ⟨a₀, ha₀⟩ := hU
  let inclusion : ↥S ↪ A := ⟨Subtype.val, Subtype.val_injective⟩
  let T := U.map inclusion
  have hsub : T ⊆ S := by
    intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    exact x.property
  have hT : T.Nonempty := ⟨a₀.val, Finset.mem_map.mpr ⟨a₀, ha₀, rfl⟩⟩
  have hretained :
      Real.exp (-(3 * (Fintype.card ι : ℝ) * (Fintype.card κ + 1) * (B + 2))) * S.card ≤
        (T.card : ℝ) := by
    simpa only [Finset.card_univ, Fintype.card_coe, T, Finset.card_map] using hlarge
  refine ⟨b a₀, ω a₀, hF a₀, T, hsub, hT, hretained, hh a₀, ?_⟩
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
  have hsame : label x = label a₀ := (hlabel_eq x hx).trans (hlabel_eq a₀ ha₀).symm
  have hb_eq : b x = b a₀ := by
    apply DFunLike.ext
    intro i
    apply e.ext_elem_iff.mpr
    intro j
    exact congrFun hsame (i, some j)
  have hω_eq : ω x = ω a₀ := by
    funext i
    exact_mod_cast (show (ω x i : ℚ) = (ω a₀ i : ℚ) from congrFun hsame (i, none))
  change witness (b a₀) (ω a₀) (hF a₀) x.val
  exact transport hb_eq hω_eq (hW x)

/-- First select a common adapted basis, then select a common fast algebra and
denominator. The factor symbols can depend on the chosen adapted basis. -/
theorem exists_common_varying_basis_controlled_dilation_factors
    {A σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis κ ℚ L) (S : Finset A) (hS : S.Nonempty)
    (η : A → L →ₗ[ℚ] ℚ) (side : A → σ → ℝ)
    (X : (b : Basis ι ℚ L) → (ω : ι → ℕ) →
      (∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) →
      A → F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    {B p : ℝ} (hB : 0 ≤ B) (hs : (s : ℝ) ≤ Real.exp B)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hdata : ∀ a ∈ S, ∃ (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})),
      (∀ i j, rationalLogHeight (e.repr (b i) j) ≤ B) ∧
      F.ControlledSymbolFactorization b ω hF (η a) (side a) (X b ω hF a) p) :
    ∃ (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
        (W : LieSubalgebra ℚ F.AssociatedGraded) (l : ℕ)
        (u : ι → F.AssociatedGraded) (T : Finset A),
      T ⊆ S ∧ T.Nonempty ∧
      Real.exp (-(3 * (Fintype.card ι : ℝ) * (Fintype.card κ + 1) * (B + 2) +
        ((p + 2) ^ 5 + p))) * (S.card : ℝ) ≤ T.card ∧
      (∀ i j, rationalLogHeight (e.repr (b i) j) ≤ B) ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      ∀ a ∈ T,
        (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF (η a) x = 0) ∧
        F.SymbolFactorizationIn b ω hF (side a) (X b ω hF a) p l W := by
  let witness (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i})) (a : A) :=
    F.ControlledSymbolFactorization b ω hF (η a) (side a) (X b ω hF a) p
  obtain ⟨b, ω, hF, U, hUS, hU, hUlarge, hb, hfactor⟩ :=
    exists_common_bounded_adapted_basis F e S hS witness hB hs hdata
  obtain ⟨W, l, u, T, hTU, hT, hTlarge, hu, hgrade, hh, hl, hlp, hfac⟩ :=
    exists_common_controlled_dilation_factors F b ω hF U hU η side (X b ω hF) hp hd hfactor
  refine ⟨b, ω, hF, W, l, u, T, hTU.trans hUS, hT, ?_, hb, hu, hgrade, hh, hl, hlp, hfac⟩
  let C : ℝ := 3 * (Fintype.card ι : ℝ) * (Fintype.card κ + 1) * (B + 2)
  let D : ℝ := (p + 2) ^ 5 + p
  change Real.exp (-(C + D)) * (S.card : ℝ) ≤ T.card
  calc
    _ = Real.exp (-D) * (Real.exp (-C) * (S.card : ℝ)) := by
      rw [show -(C + D) = -D + -C by ring, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-D) * (U.card : ℝ) :=
      mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
    _ ≤ _ := hTlarge

end PrimeUniformity

#print axioms PrimeUniformity.exists_common_bounded_adapted_basis
#print axioms PrimeUniformity.exists_common_varying_basis_controlled_dilation_factors
