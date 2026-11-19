import UpstreamPrimeRankIteration
import PrimeUniformity.PrimeCorrelationScale
import OAI.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
import OAI.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing

namespace PrimeUniformity

open Filter Module OAI.Erdos3

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- Choose a native basis adapted to the degree and rank filtration before
applying the dilation estimates, preserving the progression evaluations. -/
theorem nativeRankedPrimeTest_exists_adapted {s r X : ℕ} {p : ℝ}
    (W : NativeRankedPrimeTest s r X p) (hp : 0 ≤ p) :
    ∃ V : NativeRankedPrimeTest s r X (rankAdaptedNiltestBudget p),
      V.test.eval = W.test.eval ∧
      (W.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 W.test.test.orbit = 1 →
        V.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 V.test.test.orbit = 1) ∧
      ∃ ω : Fin V.test.dim → ℕ,
        ∀ j, V.test.model.filtration.layer j = Submodule.span ℚ (V.test.model.basis '' {i | j ≤ ω i}) := by
  obtain ⟨F, hF, hb, _⟩ := W.rank.exists_rank_adapted_data hp W.complexity
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (W.test.model.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let q := rankAdaptedNiltestBase p
  have hpow : 0 ≤ (p + 3) ^ (11 : ℕ) := by positivity
  have hpq : p ≤ q := by dsimp only [q, rankAdaptedNiltestBase]; linarith
  have hfq : (p + 3) ^ (11 : ℕ) ≤ q := by dsimp only [q, rankAdaptedNiltestBase]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp only [q, rankAdaptedNiltestBase]; linarith))
  have hqb : q ≤ rankAdaptedNiltestBudget p := le_add_of_nonneg_right (sq_nonneg _)
  let T := F.toAdaptedModelData.rebaseNiltest H hH W.test.test
  have hT : T.ComplexityLE (rankAdaptedNiltestBudget p) :=
    F.toAdaptedModelData.rebaseNiltest_complexity H hH W.test.test hq
      (W.test.complexity.mono hpq) (hF.1.mono F.model hfq) hHq
  let V : NativePrimeTest s X (rankAdaptedNiltestBudget p) :=
    { L := W.test.L, dim := finrank ℚ W.test.L, model := F.model, test := T, complexity := hT
      bound := W.test.bound
      U := W.test.U, V := W.test.V, q := W.test.q, a := W.test.a, endpoints := W.test.endpoints }
  exact ⟨⟨V, F.rank, hF.mono F.rank (hfq.trans hqb)⟩, rfl, fun h => h, F.weight, F.layers⟩

/-- Normalize the basepoint on the same model before extracting the
original-orbit coefficients, keeping the rank and progression evaluations. -/
theorem nativeRankedPrimeTest_exists_normalized (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r X : ℕ} {p : ℝ} (W : NativeRankedPrimeTest s r X p), 0 ≤ p →
      ∃ V : NativeRankedPrimeTest s r X ((p + C) ^ C), V.test.eval = W.test.eval ∧
        V.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 V.test.test.orbit = 1 := by
  obtain ⟨C, hC, hnormalize⟩ := RationalFilteredNilmanifold.exists_controlled_basepoint_normalization s
  refine ⟨C, hC, ?_⟩
  intro r X p W hp
  obtain ⟨T, hB, hT, hzero, heval⟩ := hnormalize W.test.model W.test.test hp W.test.complexity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hb : p ≤ (p + C) ^ C := (by linarith : p ≤ p + C).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C)
      (show 1 ≤ C by omega))
  let V : NativePrimeTest s X ((p + C) ^ C) :=
    { W.test with test := T, complexity := hT, bound := by rw [hB]; exact W.test.bound }
  refine ⟨⟨V, W.rank, W.complexity.mono W.rank hb⟩, ?_, hzero⟩
  funext n
  simp only [V, NativePrimeTest.eval, heval]

/-- Apply the fixed-cutoff Vaughan alternative to the actual progression
support and orbit evaluations of a native test. -/
theorem eventually_nativePrimeTest_vaughan_cases :
    ∀ᶠ X : ℕ in atTop, ∀ (s : ℕ) (p : ℝ), max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
      p ≤ Real.log (X : ℝ) ^ (1 / 20 : ℝ) → ∀ W : NativePrimeTest s X p,
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.eval →
      let A := (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val)
      let F : ℕ → ℂ := fun n => W.test.eval (fun _ => (n : ℤ))
      (W.q : ℝ) < Real.exp (11 * p) ∧
        (DenseTypeIPrefixes X X.sqrt A F (Real.exp (-20 * p)) ∨
          ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
            (X : ℝ) * Real.exp (-20 * p) <
              ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖) := by
  filter_upwards [eventually_prime_cramer_fourth_root_correlation_cases] with X hCases
  intro s p hp hpX W hlarge
  letI : NeZero W.q := ⟨W.endpoints.2.2.ne'⟩
  apply hCases W.endpoints.1 W.endpoints.2.1 W.a.val_lt
    (fun n => W.test.eval (fun _ => n)) (fun n => (W.test.norm_eval_le _).trans W.bound)
    p hp hpX
  rw [ZMod.natCast_zmod_val]
  unfold NativePrimeTest.eval at hlarge
  exact hlarge

end PrimeUniformity

#print axioms PrimeUniformity.nativeRankedPrimeTest_exists_adapted
#print axioms PrimeUniformity.nativeRankedPrimeTest_exists_normalized
#print axioms PrimeUniformity.eventually_nativePrimeTest_vaughan_cases
