import PrimeUniformity.PrimeCorrelationScale
import UpstreamTypeII

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

/-- A large masked Vaughan block for a native test gives a dense family of
actual dilated pair-symbol factorizations on a common physical scale. -/
theorem exists_native_typeII_dilation_family (s : ℕ) (hs : 1 ≤ s) :
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
      (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X U V i j A f‖ →
      ∃ J ⊆ M ×ˢ M, Real.exp (-153 * p) * ((2 : ℝ) ^ j) ^ 2 ≤ (J.card : ℝ) ∧
        ∀ v ∈ J,
          let g := T.scalarAffinePullback (v.1 : ℚ) (fun _ => 0)
          let g' := (T.scalarAffinePullback (v.2 : ℚ) (fun _ => 0)).conjugate
          ∃ (basis : Basis (Fin (finrank ℚ (PairAlgebra L L))) ℚ (PairAlgebra L L))
            (ω : Fin (finrank ℚ (PairAlgebra L L)) → ℕ)
            (hF : ∀ k, (pi (pairModels D D)).filtration.layer k =
              Submodule.span ℚ (basis '' {i | k ≤ ω i})),
            (∀ k l, rationalLogHeight ((pi (pairModels D D)).basis.repr (basis k) l) ≤
              (111 * p + C) ^ C) ∧
            (pi (pairModels D D)).filtration.ControlledSymbolFactorization basis ω hF
              (pairFrequency η (-η)) (fun _ => (2 : ℝ) ^ i)
              (pairOrbitSymbol D D g.orbit g'.orbit basis ω hF)
              ((111 * p + C) ^ C + (s : ℝ) * (121 * p + 11 * p)) := by
  obtain ⟨C, hC, happly⟩ := exists_native_typeII_dilation_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro L _ _ n _ _ _ _ D T η p hT hnorm hη hvert X U V i j a b q z hX hbX hq hp hqp hscale
    f A M hlarge
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp' : p ≤ 111 * p := by linarith
  have hf (x : ℕ) : ‖f x‖ ≤ 1 := (T.norm_eval_le _).trans hnorm
  obtain ⟨r, _, J, hJ, hsize, hsamples⟩ :=
    exists_dense_typeII_progression_samples hX hbX hq f hf hp hqp hlarge
  refine ⟨J, hJ, hsize, ?_⟩
  intro v hv
  obtain ⟨lo, hi, hlohi, hlen, hmean⟩ := hsamples v hv
  exact happly D (111 * p) (hp₂.trans hp') T (hT.mono hp') η
    (fun k => (hη k).trans hp') hvert v.1 v.2 q r lo hi hq hlohi (hscale.trans hlen)
    (by simpa only [f, neg_mul] using hmean) ((2 : ℝ) ^ i) (121 * p) (11 * p)
    (by positivity) (by linarith) (by linarith) hqp (by simpa only [neg_mul] using hlen)

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeII_dilation_family
