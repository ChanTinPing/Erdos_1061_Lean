import UpstreamPrimePreparedRankStep

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- A handler for one Vaughan branch at degree `k + 1`, on the actual
progression support and orbit of the prepared ranked test. -/
def NativePrimePreparedRankBranch (k : ℕ)
    (branch : ℕ → ℝ → Finset ℕ → (ℕ → ℂ) → Prop) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ r < k + 1, ∀ p : ℝ,
      max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ C ≤ Real.log (X : ℝ) ^ b →
      ∀ W : NativeRankedPrimeTest (k + 1) (r + 1) X p,
      ∀ ω : Fin W.test.dim → ℕ,
      (∀ j, W.test.model.filtration.layer j =
        Submodule.span ℚ (W.test.model.basis '' {i | j ≤ ω i})) →
      W.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 W.test.test.orbit = 1 →
      ∀ η : W.test.L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (W.test.model.basis i)) ≤ p) →
      (∀ z ∈ W.test.model.filtration.realification.subgroup (k + 1), ∀ x,
        W.test.test.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * W.test.test.observable x) →
      (∃ z ∈ W.rank.realSubgroup (k + 1) (r + 1), realifyFunctional η z.coord ≠ 0) →
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.test.eval →
      (W.test.q : ℝ) < Real.exp (11 * p) →
      let A := (Finset.Ioc W.test.U W.test.V).filter (fun n => n % W.test.q = W.test.a.val)
      let F : ℕ → ℂ := fun n => W.test.test.eval (fun _ => (n : ℤ))
      branch X p A F →
      ∃ G : NativeRankedPrimeTest (k + 1) r X (p ^ C),
        Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval

abbrev NativePrimePreparedTypeIBranch (k : ℕ) : Prop :=
  NativePrimePreparedRankBranch k fun X p A F =>
    DenseTypeIPrefixes X X.sqrt A F (Real.exp (-20 * p))

abbrev NativePrimePreparedTypeIIBranch (k : ℕ) : Prop :=
  NativePrimePreparedRankBranch k fun X p A F =>
    ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
      (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖

/-- A fixed finite range of degrees admits common budgets for both Vaughan
branches. The retained tests keep their progression and orbit evaluations. -/
theorem native_prime_prepared_rank_step_descent_of_branches {S : ℕ}
    (hI : ∀ k < S, NativePrimePreparedTypeIBranch k)
    (hII : ∀ k < S, NativePrimePreparedTypeIIBranch k) : NativePrimePreparedRankStepDescent S := by
  classical
  have hI' (k : Fin S) := hI k.val k.isLt
  have hII' (k : Fin S) := hII k.val k.isLt
  unfold NativePrimePreparedTypeIBranch NativePrimePreparedRankBranch at hI'
  unfold NativePrimePreparedTypeIIBranch NativePrimePreparedRankBranch at hII'
  choose CI hCI bI hbI hIevent using hI'
  choose CII hCII bII hbII hIIevent using hII'
  let C := 1 + ∑ k : Fin S, (CI k + CII k)
  have hC (k : Fin S) : CI k ≤ C ∧ CII k ≤ C := by
    have hk := Finset.single_le_sum (f := fun j : Fin S => CI j + CII j)
      (fun j _ => Nat.zero_le (CI j + CII j)) (Finset.mem_univ k)
    dsimp only [C]
    omega
  have hsmall (I : Finset (Fin S)) : ∃ b : ℝ, 0 < b ∧ ∀ k ∈ I, b ≤ bI k ∧ b ≤ bII k := by
    induction I using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i I hi ih =>
      obtain ⟨a, ha, hIa⟩ := ih
      let b := min a (min (bI i) (bII i))
      refine ⟨b, lt_min ha (lt_min (hbI i) (hbII i)), ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (min_le_right _ _).trans (min_le_right _ _)⟩
      · exact ⟨(min_le_left _ _).trans (hIa k hk).1, (min_le_left _ _).trans (hIa k hk).2⟩
  obtain ⟨b, hb, hB⟩ := hsmall Finset.univ
  have hAllI := Filter.eventually_all.mpr hIevent
  have hAllII := Filter.eventually_all.mpr hIIevent
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC₁ : 1 ≤ C := by dsimp only [C]; omega
  refine ⟨C, hC₁, b, hb, ?_⟩
  filter_upwards [hAllI, hAllII, hlog.eventually_ge_atTop 1] with X hIat hIIat hLog
  intro k hk r hr p hp hpX W ω hω hNorm η hHeight hVertical hNonzero hCorr hq A F hcase
  let j : Fin S := ⟨k, hk⟩
  have hp₁ : 1 ≤ p := (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hp)
  have hInput (K : ℕ) (a : ℝ) (hK : K ≤ C) (ha : b ≤ a) : p ^ K ≤ Real.log (X : ℝ) ^ a :=
    (pow_le_pow_right₀ hp₁ hK).trans (hpX.trans (Real.rpow_le_rpow_of_exponent_le hLog ha))
  have hOutput (K : ℕ) (hK : K ≤ C) :
      (∃ G : NativeRankedPrimeTest (k + 1) r X (p ^ K),
        Real.exp (-(p ^ K)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval) →
      ∃ G : NativeRankedPrimeTest (k + 1) r X (p ^ C),
        Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval := by
    rintro ⟨G, hG⟩
    have hKC : p ^ K ≤ p ^ C := pow_le_pow_right₀ hp₁ hK
    let G' : NativeRankedPrimeTest (k + 1) r X (p ^ C) :=
      ⟨{ G.test with complexity := G.test.complexity.mono hKC }, G.rank, G.complexity.mono G.rank hKC⟩
    exact ⟨G', (Real.exp_le_exp.mpr (neg_le_neg hKC)).trans_lt hG⟩
  rcases hcase with hcase | hcase
  · apply hOutput (CI j) (hC j).1
    exact hIat j r hr p hp (hInput (CI j) (bI j) (hC j).1 (hB j (Finset.mem_univ j)).1)
      W ω hω hNorm η hHeight hVertical hNonzero hCorr hq hcase
  · apply hOutput (CII j) (hC j).2
    exact hIIat j r hr p hp (hInput (CII j) (bII j) (hC j).2 (hB j (Finset.mem_univ j)).2)
      W ω hω hNorm η hHeight hVertical hNonzero hCorr hq hcase

/-- A family of Type I and Type II handlers supplies the concrete native
step descent used by the prime–Cramér uniformity reduction. -/
theorem native_prime_step_descent_of_prepared_branches {S : ℕ}
    (hI : ∀ k < S, NativePrimePreparedTypeIBranch k)
    (hII : ∀ k < S, NativePrimePreparedTypeIIBranch k) : PrimeCramerStepDescent S nativePrimeTests :=
  native_prime_step_descent_of_rank_step
    (native_prime_rank_step_descent_of_prepared (native_prime_prepared_rank_step_descent_of_branches hI hII))

end PrimeUniformity
