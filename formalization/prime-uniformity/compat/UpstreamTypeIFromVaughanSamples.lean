import UpstreamTypeISamples
import PrimeUniformity.UpstreamTypeICommonOrbitRecovery
import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

theorem typeI_dyadic_scale_bounds {X i : ℕ} (hX : 0 < X) (hi : i ≤ Nat.log 2 X.sqrt) :
    let L := 2 ^ (i + 1) - 1
    0 < L ∧ L ≤ X ∧ (X : ℝ) / L ≤ (X : ℝ) / (2 : ℝ) ^ i := by
  intro L
  let k : ℕ := 2 ^ i
  have hk : 0 < k := pow_pos (by decide) _
  have hL : L = 2 * k - 1 := by
    change 2 ^ (i + 1) - 1 = 2 * 2 ^ i - 1
    rw [pow_succ, Nat.mul_comm (2 ^ i) 2]
  have hkL : k ≤ L := by rw [hL]; omega
  have hksqrt : k ≤ X.sqrt :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans
      (Nat.pow_log_le_self 2 (Nat.sqrt_pos.mpr hX).ne')
  have hsqZ : 2 * (k : ℤ) ≤ (k : ℤ) ^ 2 + 1 := by nlinarith [sq_nonneg ((k : ℤ) - 1)]
  have hsq : 2 * k ≤ k ^ 2 + 1 := by exact_mod_cast hsqZ
  have hLX : L ≤ X := calc
    L ≤ k ^ 2 := by rw [hL]; omega
    _ ≤ X.sqrt ^ 2 := Nat.pow_le_pow_left hksqrt _
    _ ≤ X := Nat.sqrt_le' _
  refine ⟨hk.trans_le hkL, hLX, ?_⟩
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  exact_mod_cast (show 2 ^ i ≤ L from hkL)

theorem typeI_vaughan_sample_complexity_ge (s C : ℕ) (hC : 2 ≤ C) {p : ℝ} (hp : 2 ≤ p) :
    p ≤ (21 * p + C) ^ C + (s : ℝ) * (21 * p + 11 * p) := by
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ 21 * p + (C : ℝ) := by linarith only [hp, hC']
  have hpow : 21 * p + C ≤ (21 * p + (C : ℝ)) ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ C by omega)
  exact (by linarith only [hp, hC'] : p ≤ 21 * p + (C : ℝ)).trans
    (hpow.trans (le_add_of_nonneg_right (by positivity)))

/-- Pass from the actual dense Vaughan Type I alternative to the native
orbit recovery conditions, retaining the fast algebra and its original
top frequency cancellation. -/
theorem exists_native_typeI_orbit_recovery_from_vaughan (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V : Type} [LieRing V] [LieAlgebra ℚ V] {n r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
      (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
      (T : D.Niltest (fun _ : Unit => 1)) (η : V →ₗ[ℚ] ℚ) (p : ℝ),
      2 ≤ p → R.ComplexityLE p → T.ComplexityLE p → T.normBound ≤ 1 →
      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 T.orbit = 1 →
      (∀ k, rationalLogHeight (η (D.basis k)) ≤ p) →
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ {X a b q z : ℕ}, 0 < X → b ≤ X → 0 < q → (q : ℝ) ≤ Real.exp (11 * p) →
      Real.exp ((21 * p + C) ^ C) ≤ Real.exp (-21 * p) * ((X : ℝ) / X.sqrt) →
      let f : ℕ → ℂ := fun x => T.eval (fun _ => (x : ℤ))
      let A := (Finset.Ioc a b).filter (fun m => m % q = z)
      let P := (21 * p + C) ^ C + (s : ℝ) * (21 * p + 11 * p)
      let ρ := Real.exp (-((P + 2) ^ 5 + P + 21 * p))
      DenseTypeIPrefixes X X.sqrt A f (Real.exp (-20 * p)) →
      ∃ i ≤ Nat.log 2 X.sqrt,
      let L := 2 ^ (i + 1) - 1
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (l : ℕ) (S : Finset ℕ),
        S ⊆ dyadicDilationInterval L ∧
        ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ) ∧
        0 < l ∧ (l : ℝ) ≤ Real.exp P ∧
        (∀ x ∈ W, basisGradeProjection (D.filtration.associatedGradedBasis D.basis ω hF) ω s x = x →
          D.filtration.gradedFrequency D.basis ω hF η x = 0) ∧
        (∀ x ∈ D.filtration.gradedRefiltrationLayer W s, η x = 0) ∧
        NativeTypeIOrbitRecovery D R W T.orbit p P ρ (X : ℝ) L l := by
  obtain ⟨C, hC, sample⟩ := exists_native_typeI_common_dilation_family s hs
  refine ⟨C, hC, ?_⟩
  intro V _ _ n r _ _ _ _ D R ω hF T η p hp hRank hT hnorm hNorm hη hvert X a b q z hX hbX hq hqp hlong
    f A P ρ hDense
  obtain ⟨i, hi, W, l, u, S, hS, _, hSsize, hu, _, hUheight, hl, hlp, hTop, hSFactors⟩ :=
    sample D ω hF T η p hp hT hnorm hη hvert hX hbX hq hqp hlong hDense
  let L := 2 ^ (i + 1) - 1
  obtain ⟨hL, hLX, hSide⟩ := typeI_dyadic_scale_bounds hX hi
  have hSdyadic : S ⊆ dyadicDilationInterval L := by
    change S ⊆ dyadicDilationInterval (2 ^ (i + 1) - 1)
    rw [dyadicDilationInterval_pow_sub_one]
    intro d hd
    obtain ⟨_, _, hlo, hhi⟩ := mem_dyadicFactorBlock.mp (hS hd)
    exact Finset.mem_Ico.mpr ⟨hlo, hhi⟩
  have hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [L, card_dyadicDilationInterval_pow_sub_one, Nat.cast_pow, Nat.cast_ofNat] using hSsize
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hpP : p ≤ P := typeI_vaughan_sample_complexity_ge s C hC hp
  have hn : (n : ℝ) ≤ P := hT.1.1.trans hpP
  have hfastTop := D.filtration.frequency_zero_on_refiltered_top D.basis ω hF W η hTop
  refine ⟨i, hi, W, l, S, hSdyadic, hdense, hl, hlp, hTop, hfastTop, ?_⟩
  exact exists_native_typeI_orbits_of_common_factors D R hs ω hF T hNorm W u hu hp₀ (hp₀.trans hpP)
    hn hRank hUheight L l hL hl (Real.exp_pos _) (Nat.cast_le.mpr hLX) hSide S hSdyadic hdense hSFactors

end PrimeUniformity

#print axioms PrimeUniformity.exists_native_typeI_orbit_recovery_from_vaughan
#print axioms PrimeUniformity.typeI_dyadic_scale_bounds
