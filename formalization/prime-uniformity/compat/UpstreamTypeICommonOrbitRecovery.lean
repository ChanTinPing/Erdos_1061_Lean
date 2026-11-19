import PrimeUniformity.UpstreamTypeICommonRows
import PrimeUniformity.UpstreamTypeINativeFactorTransport
import PrimeUniformity.UpstreamTypeIOrbitRecovery

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

/-- Bounded fast-layer data and the orbit factorization available once the
dyadic recovery and coefficient-lifting inequalities hold. -/
def NativeTypeIOrbitRecovery {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (p P ρ X : ℝ) (L l : ℕ) : Prop :=
    let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    let B := ⌈Real.exp ((((2 * P + Z) + 1) + 2) ^ 7)⌉₊
    let N := Fintype.card (Fin n) * (s + 1) * 2 ^ s
    let A := B ^ N
    let H := (l : ℝ) * (N : ℝ) * (A : ℝ) * Real.exp P
    let w : Unit → ℕ := fun _ => 1
    (∀ j : Fin s, ∃ e : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (j.val + 1)),
        ∀ i k, rationalLogHeight (D.basis.repr (e i : V) k) ≤ Z) ∧
    ∃ m : Fin s → ℕ, (∀ j, m j ≤ n) ∧
    ∃ c : ∀ j, Fin (m j) → ℕ, (∀ j i, 0 < c j i ∧ c j i ≤ A * l) ∧
      ∀ (cutoff : ℕ) (p' : ℝ), 16 ≤ ρ * cutoff → 16 * (cutoff : ℝ) * H ≤ X / L →
        (∀ j : Fin s, ((cutoff * WeylInverse.leadingInverseBudget (j.val + 1) cutoff : ℕ) : ℝ) * H ≤ X / L) →
        0 ≤ p' → (n : ℝ) ≤ p' → (B : ℝ) ≤ Real.exp p' → Real.exp (separationBudget p') ≤ X →
        let Q (u : Σ j : Fin s, Fin (m j)) := typeIRowDenominatorBound cutoff (u.1.val + 1) ρ * c u.1 u.2
        ((↑(∏ u, Q u) : ℝ) ≤ Real.exp p') →
        (∀ j : Fin s, (↑(∏ u, Q u) : ℝ) * typeIRowErrorBound cutoff (j.val + 1) ρ H ≤ Real.exp p') →
        ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((s : ℝ) * (p' + 2) ^ 36) ∧
          ∃ ε K U γ : D.filtration.realification.PolynomialOrbit w,
            D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
            D.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧
            D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
            D.filtration.realification.polynomialOrbitEval w 0 γ = 1 ∧
            CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => X)
              (Real.exp ((p' + 2) ^ 18 + p')) ε.log ∧
            CoefficientGrid (D.basis.baseChange ℝ) M γ.log ∧ ε * K * U * γ = g ∧
            ∀ j : Fin s,
              coefficients K.log (Finsupp.single () (j.val + 1)) ∈
                (R.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients U.log (Finsupp.single () (j.val + 1)) ∈
                (D.filtration.gradedRefiltrationLayer W (j.val + 1)).baseChange ℝ

/-- Compose the bounded rows of a common native fast algebra with the
actual affine-pullback factorizations on the sampled dyadic band. The
displayed inequalities are the thresholds for Weyl recovery and lifting. -/
theorem exists_native_typeI_orbits_of_common_factors
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (ω : Fin n → ℕ) (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (T : D.Niltest (fun _ : Unit => 1))
    (hNorm : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 T.orbit = 1)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (u : Fin n → D.filtration.AssociatedGraded)
    (hu : Submodule.span ℚ (Set.range u) = W.toSubmodule)
    {p P : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hRank : R.ComplexityLE p)
    (hHeight : ∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) k) ≤ P)
    (L l : ℕ) {ρ X H₀ : ℝ} (hL : 0 < L) (hl : 0 < l) (hρ : 0 < ρ) (hLX : (L : ℝ) ≤ X)
    (hSide : X / L ≤ H₀) (S : Finset ℕ) (hS : S ⊆ dyadicDilationInterval L)
    (hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ))
    (hfactors : ∀ d ∈ S, D.filtration.SymbolFactorizationIn D.basis ω hF (fun _ : Unit => H₀)
      ((T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF) P l W) :
    NativeTypeIOrbitRecovery D R W T.orbit p P ρ X L l := by
  unfold NativeTypeIOrbitRecovery
  intro Z B N A H w
  obtain ⟨hFast, hB, m, hm, row, η, hann, hcol, hker, hη, hread⟩ :=
    exists_native_typeI_common_rows D R ω hF W u hu hp hP hn hRank hHeight
  let G := R.filtration
  let F := G.associatedDegree
  let hF' : ∀ d, F.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}) := fun d =>
    (congrArg (fun M : NilpotentLieFiltration V s => M.layer d) R.associated).trans (hF d)
  let W' : LieSubalgebra ℚ F.AssociatedGraded :=
    cast (congrArg (fun M : NilpotentLieFiltration V s => LieSubalgebra ℚ M.AssociatedGraded) R.associated.symm) W
  let gRank : F.realification.PolynomialOrbit w := R.orbitEquiv w T.orbit
  let Xg : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfPolynomial D.basis ω hF' w gRank.log⟩
  have hFac (d : ℕ) (hd : d ∈ S) : F.SymbolFactorizationIn D.basis ω hF' (fun _ : Unit => H₀)
      (F.realPolynomialSymbolDilationHom w (d : ℚ) Xg) P l W' :=
    native_typeI_pullback_factorization_for_rank_orbit D R ω hF T W d l H₀ P (hfactors d hd)
  have hX : 0 < X := (Nat.cast_pos.mpr hL).trans_le hLX
  have hY : 0 < X / L := div_pos hX (Nat.cast_pos.mpr hL)
  obtain ⟨c, hc, hNear⟩ := exists_typeI_projected_rows_of_common_symbol_factors
    (J := fun j => Fin (m j)) G hs D.basis ω hF' gRank row W' P l hl S hY hSide hB hFac hann hcol
  refine ⟨hFast, m, hm, c, hc, ?_⟩
  intro cutoff p' hRρ hfreq hden hp' hn' hBp' hX' Q hQ hError
  have hH : 0 ≤ H := by
    change 0 ≤ (l : ℝ) * (N : ℝ) * (A : ℝ) * Real.exp P
    positivity
  have hJ' (j : Fin s) : (Fintype.card (Fin (m j)) : ℝ) ≤ p' := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr (hm j)).trans hn'
  apply exists_typeI_rank_two_orbits_of_projected_rows D R hs W ω hF T.orbit hNorm η hker row c
    (fun j k => (hc j k).1) L cutoff hL hρ hH hLX hRρ hfreq hden S hS hdense
    hB hη hp' hn' hJ' hBp' hX' hQ hError
  · intro j i
    have hh := hread T.orbit j i
    have hglog : gRank.log = T.orbit.log := R.orbitEquiv_log w T.orbit
    exact hh.trans (congrArg (fun g => realifyCoordinateMap (η j)
      (coefficients g (typeIMonomial (j.val + 1))) i) hglog.symm)
  · exact hNear

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_orbits_of_common_factors
