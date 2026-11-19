import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

private theorem typeI_symbol_factorization_cast {V ι : Type*} [LieRing V] [LieAlgebra ℚ V]
    {s : ℕ} {F G : NilpotentLieFiltration V s} (h : F = G)
    (b : Basis ι ℚ V) (ω : ι → ℕ)
    (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ ω i}))
    (hG : ∀ d, G.layer d = Submodule.span ℚ (b '' {i | d ≤ ω i}))
    (p₀ p₁ : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] V)) (hlog : p₁ = p₀)
    (W : LieSubalgebra ℚ F.AssociatedGraded) (d l : ℕ) (H P : ℝ) :
    let w : Unit → ℕ := fun _ => 1
    let W' := cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) h) W
    F.SymbolFactorizationIn b ω hF (fun _ : Unit => H)
      (F.realPolynomialSymbolDilationHom w (d : ℚ) ⟨F.realSymbolOfPolynomial b ω hF w p₀⟩) P l W →
    G.SymbolFactorizationIn b ω hG (fun _ : Unit => H)
      (G.realPolynomialSymbolDilationHom w (d : ℚ) ⟨G.realSymbolOfPolynomial b ω hG w p₁⟩) P l W' := by
  subst G
  subst p₁
  exact fun hfactor => hfactor

/-- The common native affine-pullback factorization is the scalar dilation
of the corresponding rank-filtration symbol, with the same fast algebra,
grid denominator and smooth bound. -/
theorem native_typeI_pullback_factorization_for_rank_orbit
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s n r : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : Unit => 1)) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (d l : ℕ) (H P : ℝ)
    (hnative : D.filtration.SymbolFactorizationIn D.basis ω hF (fun _ : Unit => H)
      ((T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF) P l W) :
    let w : Unit → ℕ := fun _ => 1
    let F := R.filtration.associatedDegree
    let hF' : ∀ j, F.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}) := fun j =>
      (congrArg (fun M : NilpotentLieFiltration V s => M.layer j) R.associated).trans (hF j)
    let W' : LieSubalgebra ℚ F.AssociatedGraded :=
      cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) R.associated.symm) W
    let g : F.realification.PolynomialOrbit w := R.orbitEquiv w T.orbit
    let Xg : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfPolynomial D.basis ω hF' w g.log⟩
    F.SymbolFactorizationIn D.basis ω hF' (fun _ : Unit => H)
      (F.realPolynomialSymbolDilationHom w (d : ℚ) Xg) P l W' := by
  intro w F hF' W' g Xg
  rw [T.scalarAffinePullback_symbol] at hnative
  exact typeI_symbol_factorization_cast R.associated.symm D.basis ω hF hF' T.orbit.log g.log
    (R.orbitEquiv_log w T.orbit) W d l H P hnative

end PrimeUniformity

#print axioms PrimeUniformity.native_typeI_pullback_factorization_for_rank_orbit
