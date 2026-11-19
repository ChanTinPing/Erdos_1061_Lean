import UpstreamTypeIISamples
import UpstreamCommonAdaptedBasis

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

/-- The actual Type II samples admit a shared adapted basis, fast
subalgebra and rational denominator on a dense set of dilation pairs. -/
theorem exists_native_typeII_common_dilation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {n : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s n) (T : D.Niltest (fun _ : Unit => 1))
      (η : L →ₗ[ℚ] ℚ) (p : ℝ),
      T.ComplexityLE p → T.normBound ≤ 1 →
      (∀ k, rationalLogHeight (η (D.basis k)) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ {X U V i j a b q z : ℕ}, 1 < X → b ≤ X → 0 < q →
      max 2 (Real.log (Real.log (X : ℝ))) ≤ p → (q : ℝ) ≤ Real.exp (11 * p) →
      Real.exp ((111 * p + C) ^ C) ≤ Real.exp (-121 * p) * ((2 : ℝ) ^ i / q) →
      let f : ℕ → ℂ := fun x => T.eval (fun _ => (x : ℤ))
      let A := (Finset.Ioc a b).filter (fun m => m % q = z)
      let M := dyadicFactorBlock V X j
      let F := (pi (pairModels D D)).filtration
      let B := (111 * p + C) ^ C + (s : ℝ)
      let P := (111 * p + C) ^ C + (s : ℝ) * (121 * p + 11 * p)
      let d := finrank ℚ (PairAlgebra L L)
      (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A f‖ →
      ∃ (basis : Basis (Fin d) ℚ (PairAlgebra L L)) (ω : Fin d → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (basis '' {a | k ≤ ω a}))
        (W : LieSubalgebra ℚ F.AssociatedGraded) (l : ℕ) (u : Fin d → F.AssociatedGraded)
        (J : Finset (ℕ × ℕ)),
        J ⊆ M ×ˢ M ∧ J.Nonempty ∧
        Real.exp (-(3 * (d : ℝ) * ((d : ℝ) + 1) * (B + 2) + ((P + 2) ^ 5 + P) + 153 * p)) *
          ((2 : ℝ) ^ j) ^ 2 ≤ (J.card : ℝ) ∧
        (∀ k t, rationalLogHeight ((pi (pairModels D D)).basis.repr (basis k) t) ≤ B) ∧
        Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis basis ω hF) ω W.toSubmodule ∧
        (∀ k t, rationalLogHeight ((F.associatedGradedBasis basis ω hF).repr (u k) t) ≤ P) ∧
        0 < l ∧ (l : ℝ) ≤ Real.exp P ∧
        (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis basis ω hF) ω s x = x →
          F.gradedFrequency basis ω hF (pairFrequency η (-η)) x = 0) ∧
        ∀ v ∈ J,
          let g := T.scalarAffinePullback (v.1 : ℚ) (fun _ => 0)
          let g' := (T.scalarAffinePullback (v.2 : ℚ) (fun _ => 0)).conjugate
          F.SymbolFactorizationIn basis ω hF (fun _ => (2 : ℝ) ^ i)
            (pairOrbitSymbol D D g.orbit g'.orbit basis ω hF) P l W := by
  obtain ⟨C, hC, hfamily⟩ := exists_native_typeII_dilation_family s hs
  refine ⟨C, hC, ?_⟩
  intro L _ _ n _ _ _ _ D T η p hT hnorm hη hvert X U V i j a b q z hX hbX hq hp hqp hscale
    f A M F B P d hlarge
  obtain ⟨S, hS, hsize, hfac⟩ := hfamily D T η p hT hnorm hη hvert hX hbX hq hp hqp hscale hlarge
  have hS' : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos (Real.exp_pos _) (by positivity)).trans_le hsize))
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hBase : (111 * p + (C : ℝ)) ≤ (111 * p + (C : ℝ)) ^ C := by
    have hC' : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ 111 * p + (C : ℝ))
      (show 1 ≤ C by omega)
  have h2p : 2 * p ≤ P := by
    have hC' : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    dsimp only [P]
    exact (by linarith : 2 * p ≤ 111 * p + C).trans (hBase.trans (le_add_of_nonneg_right (by positivity)))
  have hP : 0 ≤ P := (by positivity : 0 ≤ 2 * p).trans h2p
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hbs : (s : ℝ) ≤ Real.exp B := by
    have hb : (s : ℝ) ≤ B := by dsimp only [B]; exact le_add_of_nonneg_left (by positivity)
    linarith [Real.add_one_le_exp B]
  let e := (pi (pairModels D D)).basis
  have he : Fintype.card (Fin (Fintype.card (Σ v : Bool, Fin (Bool.rec n n v)))) = d :=
    (finrank_eq_card_basis e).symm
  have hd : d = n + n := by
    rw [← he, Fintype.card_fin, Fintype.card_sigma, Fintype.sum_bool]
    simp
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ P := by
    rw [Fintype.card_fin, hd, Nat.cast_add]
    linarith [hT.1.1]
  let symbol (basis : Basis (Fin d) ℚ (PairAlgebra L L)) (ω : Fin d → ℕ)
      (hF : ∀ k, F.layer k = Submodule.span ℚ (basis '' {a | k ≤ ω a})) (v : ℕ × ℕ) :=
    pairOrbitSymbol D D (T.scalarAffinePullback (v.1 : ℚ) (fun _ => 0)).orbit
      ((T.scalarAffinePullback (v.2 : ℚ) (fun _ => 0)).conjugate).orbit basis ω hF
  have hfamily' (v : ℕ × ℕ) (hv : v ∈ S) :
      ∃ (basis : Basis (Fin d) ℚ (PairAlgebra L L)) (ω : Fin d → ℕ)
        (hF : ∀ k, F.layer k = Submodule.span ℚ (basis '' {a | k ≤ ω a})),
        (∀ k t, rationalLogHeight (e.repr (basis k) t) ≤ B) ∧
        F.ControlledSymbolFactorization basis ω hF (pairFrequency η (-η)) (fun _ => (2 : ℝ) ^ i)
          (symbol basis ω hF v) P := by
    obtain ⟨basis, ω, hF, hb, hfac⟩ := hfac v hv
    exact ⟨basis, ω, hF, fun k t => (hb k t).trans (le_add_of_nonneg_right (by positivity)), hfac⟩
  obtain ⟨basis, ω, hF, W, l, u, J, hJ, hJn, hJsize, hheight, hu, hgrade, hgu, hl, hlP, hfac⟩ :=
    exists_common_varying_basis_controlled_dilation_factors F e S hS'
      (fun _ => pairFrequency η (-η)) (fun _ _ => (2 : ℝ) ^ i) symbol hB hbs hP hdp hfamily'
  obtain ⟨v₀, hv₀⟩ := hJn
  refine ⟨basis, ω, hF, W, l, u, J, hJ.trans hS, ⟨v₀, hv₀⟩, ?_, hheight, hu, hgrade, hgu, hl, hlP,
    (hfac v₀ hv₀).1, fun v hv => (hfac v hv).2⟩
  rw [he, Fintype.card_fin] at hJsize
  let loss := 3 * (d : ℝ) * ((d : ℝ) + 1) * (B + 2) + ((P + 2) ^ 5 + P)
  change Real.exp (-(loss + 153 * p)) * ((2 : ℝ) ^ j) ^ 2 ≤ (J.card : ℝ)
  rw [show -(loss + 153 * p) = -loss + -153 * p by ring, Real.exp_add, mul_assoc]
  exact (mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le).trans hJsize

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeII_common_dilation_family
