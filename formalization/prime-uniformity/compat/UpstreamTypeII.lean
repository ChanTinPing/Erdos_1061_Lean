import UpstreamTypeI
import OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

/-- A large sampled Type II column correlation gives the upstream
controlled pair-symbol factorization on the cofactor scale. -/
theorem exists_native_typeII_dilation_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {n : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s n) (p : ℝ), 2 ≤ p →
      ∀ (T : D.Niltest (fun _ : Unit => 1)), T.ComplexityLE p →
      ∀ (η : L →ₗ[ℚ] ℚ), (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) =
          CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (d e Q r lo hi : ℕ), 0 < Q → lo ≤ hi →
      Real.exp ((p + C) ^ C) ≤ ((Finset.Icc lo hi).card : ℝ) →
      Real.exp (-p) ≤ ‖∑ x ∈ Finset.Icc lo hi,
        T.eval (fun _ => ((d * (Q * x + r) : ℕ) : ℤ)) *
          star (T.eval (fun _ => ((e * (Q * x + r) : ℕ) : ℤ)))‖ / ((Finset.Icc lo hi).card : ℝ) →
      ∀ (H a b : ℝ), 0 < H → 0 ≤ a → 0 ≤ b → (Q : ℝ) ≤ Real.exp b →
      Real.exp (-a) * (H / (Q : ℝ)) ≤ ((Finset.Icc lo hi).card : ℝ) →
      let V := T.scalarAffinePullback (d : ℚ) (fun _ => 0)
      let W := (T.scalarAffinePullback (e : ℚ) (fun _ => 0)).conjugate
      ∃ (basis : Basis (Fin (finrank ℚ (PairAlgebra L L))) ℚ (PairAlgebra L L))
        (ω : Fin (finrank ℚ (PairAlgebra L L)) → ℕ)
        (hF : ∀ k, (pi (pairModels D D)).filtration.layer k =
          Submodule.span ℚ (basis '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D D)).basis.repr (basis i) j) ≤ (p + C) ^ C) ∧
        (pi (pairModels D D)).filtration.ControlledSymbolFactorization basis ω hF
          (pairFrequency η (-η)) (fun _ => H) (pairOrbitSymbol D D V.orbit W.orbit basis ω hF)
          ((p + C) ^ C + (s : ℝ) * (a + b)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_affine_cell_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro L _ _ n _ _ _ _ D p hp T hT η hη hvertical d e Q r lo hi hQ hlo hlong hmean H a b hH ha hb
    hQexp hphysical V W
  let len := (Finset.Icc lo hi).card
  have hp₁ : 1 ≤ p := (by norm_num : (1 : ℝ) ≤ 2).trans hp
  have hσ : (Fintype.card Unit : ℝ) ≤ p := by
    simpa only [Fintype.card_unit, Nat.cast_one] using hp₁
  have hlen : 0 < len := Finset.card_pos.mpr ⟨lo, Finset.mem_Icc.mpr ⟨le_rfl, hlo⟩⟩
  have hθ (i : Fin n) : rationalLogHeight ((-η) (D.basis i)) ≤ p := by
    simpa [rationalLogHeight] using hη i
  have hvertW : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      W.observable (z • x) = CircleFourier.character
        ((realifyFunctional (-η) z.coord : ℝ) : CircleFourier.Circle) * W.observable x :=
    (T.scalarAffinePullback (e : ℚ) (fun _ => 0)).conjugate_vertical η hvertical
  have heval (f x : ℕ) :
      (T.scalarAffinePullback (f : ℚ) (fun _ => 0)).eval (fun _ => (Q : ℤ) * x + r) =
        T.eval (fun _ => ((f * (Q * x + r) : ℕ) : ℤ)) := by
    simpa only [Int.cast_natCast, Int.cast_zero, Nat.cast_add, Nat.cast_mul, add_zero] using
      T.scalarAffinePullback_eval_integer (f : ℤ) (fun _ => 0) (fun _ => (Q : ℤ) * x + r)
  have hcast : Function.Injective (fun x : ℕ => (x : ℤ)) := fun _ _ h => Int.ofNat.inj h
  have hbias : Real.exp (-p) ≤
      ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (lo : ℤ)) (fun _ => len),
        V.eval (fun i => (Q : ℤ) * x i + r) * W.eval (fun i => (Q : ℤ) * x i + r)‖ := by
    rw [unitIntervalBox_expect, ← natCast_Icc_eq_translated_Ico hlo, Finset.expect_image hcast.injOn]
    simp only [Finset.expect_eq_sum_div_card, norm_div, Complex.norm_natCast,
      V, W, Niltest.eval_conjugate, heval]
    exact hmean
  exact hstep D D V W hp ha hb hT hT Q hQ hQexp (fun _ => (r : ℤ)) η (-η)
    hη hθ hvertical hvertW (fun _ => (lo : ℤ)) (fun _ => len) (fun _ => H)
    (fun _ => hlen) (fun _ => hH) hσ (fun _ => hlong) (fun _ => hphysical) hbias

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeII_dilation_factorization
