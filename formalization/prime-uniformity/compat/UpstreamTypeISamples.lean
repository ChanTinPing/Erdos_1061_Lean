import PrimeUniformity.TypeIProgressions
import UpstreamTypeI
import UpstreamCommonDilationFactors

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

/-- The Type I alternative for a native test yields a dense family of
unmasked dilation factorizations sharing one fast algebra and denominator. -/
theorem exists_native_typeI_common_dilation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {n : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s n) (ω : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (T : D.Niltest (fun _ : Unit => 1)) (η : L →ₗ[ℚ] ℚ) (p : ℝ),
      2 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      (∀ k, rationalLogHeight (η (D.basis k)) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ {X a b q z : ℕ}, 0 < X → b ≤ X → 0 < q → (q : ℝ) ≤ Real.exp (11 * p) →
      Real.exp ((21 * p + C) ^ C) ≤ Real.exp (-21 * p) * ((X : ℝ) / X.sqrt) →
      let f : ℕ → ℂ := fun x => T.eval (fun _ => (x : ℤ))
      let A := (Finset.Ioc a b).filter (fun m => m % q = z)
      let P := (21 * p + C) ^ C + (s : ℝ) * (21 * p + 11 * p)
      DenseTypeIPrefixes X X.sqrt A f (Real.exp (-20 * p)) →
      ∃ i ≤ Nat.log 2 X.sqrt,
        let H := (X : ℝ) / (2 : ℝ) ^ i
        ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (l : ℕ)
          (u : Fin n → D.filtration.AssociatedGraded) (J : Finset ℕ),
          J ⊆ dyadicFactorBlock 0 X.sqrt i ∧ J.Nonempty ∧
          Real.exp (-((P + 2) ^ 5 + P + 21 * p)) * (2 : ℝ) ^ i ≤ (J.card : ℝ) ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω W.toSubmodule ∧
          (∀ j k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u j) k) ≤ P) ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp P ∧
          (∀ x ∈ W, basisGradeProjection (D.filtration.associatedGradedBasis D.basis ω hF) ω s x = x →
            D.filtration.gradedFrequency D.basis ω hF η x = 0) ∧
          ∀ d ∈ J, D.filtration.SymbolFactorizationIn D.basis ω hF (fun _ => H)
            ((T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF) P l W := by
  obtain ⟨C, hC, happly⟩ := exists_native_typeI_dilation_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro L _ _ n _ _ _ _ D ω hF T η p hp hT hnorm hη hvert X a b q z hX hbX hq hqp hlong f A P hDense
  have hp' : p ≤ 21 * p := by linarith
  have hP : p ≤ P := by
    have hpow : 21 * p + C ≤ (21 * p + (C : ℝ)) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ 21 * p + (C : ℝ))
        (show 1 ≤ C by omega)
    have hCnonneg : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    dsimp only [P]
    exact (by linarith : p ≤ 21 * p + C).trans (hpow.trans (le_add_of_nonneg_right (by positivity)))
  have hdim : (Fintype.card (Fin n) : ℝ) ≤ P := by
    simpa only [Fintype.card_fin] using hT.1.1.trans hP
  have hδ : Real.exp (-21 * p) ≤ Real.exp (-20 * p) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-21 * p) * Real.exp p :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp p]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, show -21 * p + p = -20 * p by ring]
  have hf (x : ℕ) (_ : x ∈ A) : ‖f x‖ ≤ 1 := (T.norm_eval_le _).trans hnorm
  obtain ⟨i, hindex, S, hS, hcount, hsamples⟩ :=
    exists_dense_large_typeI_dilation_subsums hX hbX hq f (Real.exp_pos (-20 * p)) hf hDense
  let H := (X : ℝ) / (2 : ℝ) ^ i
  let orbit (d : ℕ) := (T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF
  have hH : 0 < H := div_pos (Nat.cast_pos.mpr hX) (by positivity)
  have hcount' : Real.exp (-21 * p) * (2 : ℝ) ^ i ≤ (S.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hδ (by positivity)).trans hcount
  have hS' : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos (Real.exp_pos _) (by positivity)).trans_le hcount'))
  have hfactors d (hd : d ∈ S) : D.filtration.ControlledSymbolFactorization D.basis ω hF η
      (fun _ : Unit => H) (orbit d) P := by
    obtain ⟨r, hr, lo, hi, _, hlen, _, hmean⟩ := hsamples d hd
    let Q := q / Nat.gcd q d
    have hQ : 0 < Q := (Nat.zero_le r).trans_lt hr
    have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hQp := (show (Q : ℝ) ≤ q by exact_mod_cast Nat.div_le_self q (Nat.gcd q d)).trans hqp
    have hlen' := (mul_le_mul_of_nonneg_right hδ hH.le).trans hlen
    have hlohi := Finset.nonempty_Icc.mp (Finset.card_pos.mp (Nat.cast_pos.mp
      ((mul_pos (Real.exp_pos _) hH).trans_le hlen')))
    have hHlarge : (X : ℝ) / X.sqrt ≤ H :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by
        have h := (Nat.pow_le_pow_right (by decide : 2 > 0) hindex).trans
          (Nat.pow_log_le_self 2 (Nat.sqrt_pos.mpr hX).ne')
        exact_mod_cast h)
    have hlong' := hlong.trans ((mul_le_mul_of_nonneg_left hHlarge (Real.exp_pos _).le).trans hlen')
    have hphys : Real.exp (-(21 * p)) * (H / (Q : ℝ)) ≤ ((Finset.Icc lo hi).card : ℝ) := by
      rw [← neg_mul]
      exact (mul_le_mul_of_nonneg_left (div_le_self hH.le hQ') (Real.exp_pos _).le).trans hlen'
    exact happly D ω hF (21 * p) (by linarith) T (hT.mono hp') η
      (fun k => (hη k).trans hp') hvert d Q r lo hi hQ hlohi hlong'
      (by simpa only [f, neg_mul] using hδ.trans hmean) H (21 * p) (11 * p) hH
      (by linarith) (by linarith) hQp hphys
  obtain ⟨W, l, u, J, hJ, hne, hJsize, hu, hgrade, huheight, hl, hlp, hfac⟩ :=
    exists_common_controlled_dilation_factors D.filtration D.basis ω hF S hS'
      (fun _ => η) (fun _ _ => H) orbit (by linarith) hdim hfactors
  obtain ⟨d, hd⟩ := hne
  refine ⟨i, hindex, W, l, u, J, hJ.trans hS, ⟨d, hd⟩, ?_, hu, hgrade, huheight, hl, hlp,
    (hfac d hd).1, fun d hd => (hfac d hd).2⟩
  calc
    _ = Real.exp (-((P + 2) ^ 5 + P)) * (Real.exp (-21 * p) * (2 : ℝ) ^ i) := by
      rw [show -((P + 2) ^ 5 + P + 21 * p) = -((P + 2) ^ 5 + P) + -21 * p by ring,
        Real.exp_add, mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hcount' (Real.exp_pos _).le).trans hJsize

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_common_dilation_family
