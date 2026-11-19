import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
import OAI.Combinatorics.Progressions.Geometry.UnitIntervalBox
import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection

namespace PrimeUniformity

open OAI.Erdos3
open Module
open scoped BigOperators TensorProduct

theorem natCast_Icc_eq_translated_Ico {lo hi : ℕ} (hlo : lo ≤ hi) :
    (Finset.Icc lo hi).image (fun n : ℕ => (n : ℤ)) =
      Finset.Ico (lo : ℤ) ((lo : ℤ) + (Finset.Icc lo hi).card) := by
  have hlen : (((Finset.Icc lo hi).card : ℕ) : ℤ) = (hi : ℤ) + 1 - (lo : ℤ) := by
    rw [Nat.card_Icc, Int.natCast_sub (by omega), Nat.cast_add, Nat.cast_one]
  ext x
  rw [Finset.mem_image, Finset.mem_Ico, hlen]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have := Finset.mem_Icc.mp hn
    omega
  · intro hx
    refine ⟨x.toNat, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Int.toNat_of_nonneg ?_⟩ <;> omega

/-- A large mean of the affine Type I sample yields a controlled
factorization of the dilated orbit on the physical cofactor scale. Only
the progression stride is reversed, so its size is charged to the
rational denominator and the multiplicative factor is left for recovery
across the dense set of factors. -/
theorem exists_native_typeI_dilation_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {n : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s n) (ω : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 1 ≤ p →
      ∀ (T : D.Niltest (fun _ : Unit => 1)), T.ComplexityLE p →
      ∀ (η : L →ₗ[ℚ] ℚ), (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (d Q b lo hi : ℕ), 0 < Q → lo ≤ hi →
      Real.exp ((p + C) ^ C) ≤ ((Finset.Icc lo hi).card : ℝ) →
      Real.exp (-p) ≤
        ‖∑ x ∈ Finset.Icc lo hi, T.eval (fun _ => ((d * (Q * x + b) : ℕ) : ℤ))‖ /
          ((Finset.Icc lo hi).card : ℝ) →
      ∀ (H q r : ℝ), 0 < H → 0 ≤ q → 0 ≤ r → (Q : ℝ) ≤ Real.exp r →
      Real.exp (-q) * (H / (Q : ℝ)) ≤ ((Finset.Icc lo hi).card : ℝ) →
      D.filtration.ControlledSymbolFactorization D.basis ω hF η (fun _ => H)
        ((T.scalarAffinePullback (d : ℚ) (fun _ => 0)).symbol D.basis ω hF)
        ((p + C) ^ C + (s : ℝ) * (q + r)) := by
  obtain ⟨C, hC, hstep⟩ := exists_translated_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro L _ _ n _ _ _ _ D ω hF p hp T hT η hη hvertical d Q b lo hi hQ hlo hlong
    hmean H q r hH hq hr hQexp hphysical
  let S := Finset.Icc lo hi
  let len := S.card
  let Td := T.scalarAffinePullback (d : ℚ) (fun _ => 0)
  let V := Td.scalarAffinePullback (Q : ℚ) (fun _ => (b : ℚ))
  have hlen : 0 < len := Finset.card_pos.mpr ⟨lo, Finset.mem_Icc.mpr ⟨le_rfl, hlo⟩⟩
  have heval (x : ℕ) :
      V.eval (fun _ => (x : ℤ)) = T.eval (fun _ => ((d * (Q * x + b) : ℕ) : ℤ)) := by
    have houter := Td.scalarAffinePullback_eval_integer (Q : ℤ) (fun _ => (b : ℤ))
      (fun _ => (x : ℤ))
    have hinner := T.scalarAffinePullback_eval_integer (d : ℤ) (fun _ => (0 : ℤ))
      (fun _ => (Q : ℤ) * x + b)
    exact (by simpa only [V, Int.cast_natCast] using houter :
        V.eval (fun _ => (x : ℤ)) = Td.eval (fun _ => (Q : ℤ) * x + b)).trans
      (by simpa only [Td, Int.cast_natCast, Int.cast_zero, Nat.cast_mul, Nat.cast_add, add_zero]
        using hinner)
  have hcast : Function.Injective (fun x : ℕ => (x : ℤ)) := fun _ _ h => Int.ofNat.inj h
  have hbias : Real.exp (-p) ≤
      ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (lo : ℤ)) (fun _ => len), V.eval x‖ := by
    rw [unitIntervalBox_expect, ← natCast_Icc_eq_translated_Ico hlo, Finset.expect_image hcast.injOn]
    simp only [Finset.expect_eq_sum_div_card, norm_div, Complex.norm_natCast, heval]
    exact hmean
  have hcontrolled := hstep D ω hF p (zero_le_one.trans hp)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) V hT η hη hvertical
    (fun _ => (lo : ℤ)) (fun _ => len) (fun _ => hlen) (fun _ => hlong) hbias
  obtain ⟨m, W, v, hm, hmexp, hv, hW, hheight, hηW, hIn⟩ :=
    hcontrolled.exists_in D.filtration D.basis ω hF
  have htransport := Td.scalarAffineCell_factorization_to_original D.basis ω hF Q hQ
    (fun _ => (b : ℚ)) hIn (fun _ => by exact_mod_cast hlen) (fun _ => hH) hq
    (fun _ => hphysical)
  let B := (p + C) ^ C + (s : ℝ) * (q + r)
  have hb : (p + C) ^ C + (s : ℝ) * q ≤ B := by
    dsimp only [B]
    gcongr
    exact le_add_of_nonneg_right hr
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ :=
    htransport.mono D.filtration D.basis ω hF hb (fun _ => hH)
  have hQpow : (Q : ℝ) ^ s ≤ Real.exp ((s : ℝ) * (q + r)) := by
    calc
      _ ≤ Real.exp r ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) hQexp s
      _ = Real.exp ((s : ℝ) * r) := (Real.exp_nat_mul r s).symm
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hq) (Nat.cast_nonneg s))
  have hm' : ((m * Q ^ s : ℕ) : ℝ) ≤ Real.exp B := by
    rw [Nat.cast_mul, Nat.cast_pow, show Real.exp B =
      Real.exp ((p + C) ^ C) * Real.exp ((s : ℝ) * (q + r)) from Real.exp_add _ _]
    exact mul_le_mul hmexp hQpow (by positivity) (Real.exp_nonneg _)
  have hbase : (p + C) ^ C ≤ B :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) (add_nonneg hq hr))
  exact ⟨m * Q ^ s, E, P, R, W, v, Nat.mul_pos hm (pow_pos hQ _), hm', hprod,
    hE, hR, hv, hW, fun i j => (hheight i j).trans hbase, hηW, hP⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_dilation_factorization
