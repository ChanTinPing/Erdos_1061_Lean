import UpstreamNativePrimeTests

namespace PrimeUniformity

open Filter Module
open OAI.Erdos3
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- The remaining descent input only concerns tests with a nonzero vertical
frequency. The frequency height and correlation are measured in the same
logarithmic budget as the test. -/
def NativePrimeVerticalStepDescent (s : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ k < s, ∀ p : ℝ, max 2 (Real.log (Real.log (X : ℝ))) ≤ p →
      p ^ C ≤ Real.log (X : ℝ) ^ b → ∀ W : NativePrimeTest (k + 1) X p,
      ∀ η : W.L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (W.model.basis i)) ≤ p) →
      (∀ z ∈ W.model.filtration.realification.subgroup (k + 1), ∀ x,
        W.test.observable (z • x) =
          CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            W.test.observable x) →
      (∃ z ∈ W.model.filtration.realification.subgroup (k + 1), realifyFunctional η z.coord ≠ 0) →
      Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.eval →
      ∃ G : NativePrimeTest k X (p ^ C),
        Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.eval

/-- Select a correlated vertical component under a polynomial log budget.
The mode has the same orbit and model, so a rank structure and basepoint
normalization on the test are available for the selected component. -/
theorem nativePrimeTest_select_vertical_at_budget {s X A : ℕ} {p : ℝ}
    (hFourier : ∀ t : ℝ, 0 ≤ t → verticalDecompositionBudget t ≤ (t + A) ^ A)
    (hX : 0 < X) (hp : 2 ≤ p) (W : NativePrimeTest s X p) (w : ℤ → ℝ)
    (hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ Real.exp (9 * p))
    (hlarge : Real.exp (-p) < intervalCorrelation X w W.eval) :
    let q := 12 * p + 2 * p + (12 * p + A) ^ A
    ∃ η : W.L →ₗ[ℚ] ℚ, ∃ T : W.model.Niltest (fun _ : Unit => 1),
      T.ComplexityLE q ∧ T.normBound ≤ 1 ∧ T.orbit = W.test.orbit ∧
      (∀ i, rationalLogHeight (η (W.model.basis i)) ≤ q) ∧
      (∀ z ∈ W.model.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) ∧
      Real.exp (-q) < intervalCorrelation X w (fun n =>
        if n ∈ residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ) W.a then T.eval (fun _ => n) else 0) := by
  intro q
  let ρ := Real.exp (-(12 * p))
  have h12 : 0 ≤ 12 * p := by linarith
  have hq : 12 * p ≤ q := by dsimp only [q]; linarith [pow_nonneg (by positivity : 0 ≤ 12 * p + A) A]
  have herror : Real.exp (9 * p) * ρ = Real.exp (-3 * p) := by
    dsimp only [ρ]
    rw [← Real.exp_add, show 9 * p + -(12 * p) = -3 * p by ring]
  have hsmall : Real.exp (-3 * p) + Real.exp (-2 * p) < Real.exp (-p) := by
    have h2 : (2 : ℝ) < Real.exp p := by linarith [Real.add_one_le_exp p]
    calc
      _ ≤ 2 * Real.exp (-2 * p) := by
        have h3 := Real.exp_le_exp.mpr (show -3 * p ≤ -2 * p by linarith)
        linarith
      _ < Real.exp p * Real.exp (-2 * p) := mul_lt_mul_of_pos_right h2 (Real.exp_pos _)
      _ = _ := by rw [← Real.exp_add, show p + -2 * p = -p by ring]
  have hSEL : Real.exp (9 * p) * ρ < intervalCorrelation X w W.eval := by
    rw [herror]
    exact (lt_add_of_pos_right _ (Real.exp_pos _)).trans (hsmall.trans hlarge)
  let W₁ : NativePrimeTest s X (12 * p) := { W with complexity := W.complexity.mono (by linarith) }
  have hρinv : ρ⁻¹ ≤ Real.exp (12 * p) := by dsimp only [ρ]; rw [Real.exp_neg, inv_inv]
  obtain ⟨η, T, hT, hTbound, hOrbit, hheight, hvertical, hcorr⟩ :=
    nativePrimeTest_correlating_vertical_component_with_orbit hX h12 W₁ w (Real.exp_pos _).le
      (Real.exp_pos _) hρinv hw hSEL
  have hv : verticalDecompositionBudget (12 * p) + 2 * p ≤ q := by
    dsimp only [q]
    linarith [hFourier (12 * p) h12]
  refine ⟨η, T, hT.mono hq, hTbound, hOrbit, fun i => (hheight i).trans (by linarith), hvertical, ?_⟩
  change Real.exp (-q) < intervalCorrelation X w (W₁.withNiltest T hT hTbound).eval
  by_contra! hle
  have hprod : Real.exp (verticalDecompositionBudget (12 * p)) *
      intervalCorrelation X w (W₁.withNiltest T hT hTbound).eval ≤ Real.exp (-2 * p) := by
    refine (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (not_le_of_gt hlarge) (hcorr.trans ((add_le_add herror.le hprod).trans hsmall.le))

/-- A polynomial with natural coefficients is bounded by a power on `[2, ∞)`. -/
theorem exists_natPolynomial_eval_le_power (P : Polynomial ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : ℝ, 2 ≤ p → P.eval₂ (Nat.castRingHom ℝ) p ≤ p ^ K := by
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  have htwo (m : ℕ) : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      rw [Nat.cast_succ, pow_succ]
      linarith
  refine ⟨(N + 2) * N, Nat.mul_pos (by omega) (by omega), ?_⟩
  intro p hp
  have hp₀ : 0 ≤ p := by linarith
  have hconst := (htwo (N + 1)).trans (pow_le_pow_left₀ (by norm_num) hp (N + 1))
  have hsum : p + N ≤ p ^ (N + 2) := by
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * p := by push_cast; nlinarith
      _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_right hconst hp₀
  exact (hbound p hp₀).trans (by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hsum N)

/-- Vertical Fourier selection and the top-invariant quotient reduce
full native step descent to the nonzero-frequency case. -/
theorem native_prime_step_descent_of_vertical {s : ℕ} (h : NativePrimeVerticalStepDescent s) :
    PrimeCramerStepDescent s nativePrimeTests := by
  obtain ⟨C, hC, b, hb, hstep⟩ := h
  obtain ⟨A, hA, hFourier⟩ := exists_verticalDecompositionBudget_bound
  choose D hD hTop using nativePrimeTest_topInvariant_drop
  let M := 2 + ∑ k ∈ Finset.range s, D k
  have hDM (k : ℕ) (hk : k < s) : D k ≤ M := by
    have h := Finset.single_le_sum (f := D) (fun i _ => Nat.zero_le (D i)) (Finset.mem_range.mpr hk)
    dsimp only [M]
    omega
  let R : Polynomial ℕ := 12 * Polynomial.X + 2 * Polynomial.X +
    (12 * Polynomial.X + Polynomial.C A) ^ A
  let P : Polynomial ℕ := R ^ C + ((R + 3) ^ 11 + Polynomial.C M) ^ M
  obtain ⟨K, hK, hP⟩ := exists_natPolynomial_eval_le_power P
  obtain ⟨B, hB, hweight⟩ := eventually_abs_strictVonMangoldtCramerDifference
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨K, hK, b, hb, ?_⟩
  filter_upwards [hstep, hweight, hlog.eventually_ge_atTop B, eventually_gt_atTop (0 : ℕ)]
    with X hstep hweight hL hX
  intro k hk p hp hpK F hF hlarge
  obtain ⟨W, rfl⟩ := hF
  let L := Real.log (X : ℝ)
  let r := 12 * p + 2 * p + (12 * p + A) ^ A
  let w := strictVonMangoldtCramerDifference X
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hr12 : 12 * p ≤ r := by
    dsimp only [r]
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * p)).trans
      (le_add_of_nonneg_right (by positivity))
  have hpr : p ≤ r := (by linarith : p ≤ 12 * p).trans hr12
  have hr₂ : 2 ≤ r := hp₂.trans hpr
  have hrC : r ≤ r ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ ((by norm_num : (1 : ℝ) ≤ 2).trans hr₂) hC
  have hbudget : r ^ C + ((r + 3) ^ (11 : ℕ) + M) ^ M ≤ p ^ K := by
    simpa [P, R, r, Polynomial.eval₂_pow] using hP p hp₂
  have hCR : r ^ C ≤ p ^ K := (le_add_of_nonneg_right (by positivity)).trans hbudget
  have hTopR : ((r + 3) ^ (11 : ℕ) + (D k : ℝ)) ^ (D k) ≤ p ^ K := by
    have hDM' : (D k : ℝ) ≤ M := by exact_mod_cast hDM k hk
    have h₀ : 0 ≤ (r + 3) ^ (11 : ℕ) + (D k : ℝ) := by positivity
    have h₁ : 1 ≤ (r + 3) ^ (11 : ℕ) + (M : ℝ) := by
      have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by dsimp [M]; omega)
      exact hM.trans (le_add_of_nonneg_left (by positivity))
    exact ((pow_le_pow_left₀ h₀ (add_le_add le_rfl hDM') (D k)).trans
      (pow_le_pow_right₀ h₁ (hDM k hk))).trans ((le_add_of_nonneg_left (by positivity)).trans hbudget)
  have hL₀ : 0 ≤ L := (zero_le_one.trans hB).trans hL
  have hLe : L ≤ Real.exp p :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans_le (hB.trans hL))).mp ((le_max_right _ _).trans hp)
  have hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ Real.exp (9 * p) := by
    intro n hn
    calc
      _ ≤ B * L ^ (8 : ℕ) := hweight n hn
      _ ≤ L ^ (9 : ℕ) := by
        rw [pow_succ' L 8]
        exact mul_le_mul_of_nonneg_right hL (pow_nonneg hL₀ 8)
      _ ≤ Real.exp p ^ (9 : ℕ) := pow_le_pow_left₀ hL₀ hLe 9
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  obtain ⟨η, T, hT, hTbound, _, hheight', hvertical, hV⟩ :=
    nativePrimeTest_select_vertical_at_budget hFourier hX hp₂ W w hw hlarge
  let V : NativePrimeTest (k + 1) X r :=
    { W with test := T, complexity := hT, bound := hTbound }
  obtain ⟨G, hG⟩ : ∃ G : NativePrimeTest k X (p ^ K),
      Real.exp (-(p ^ K)) < intervalCorrelation X w G.eval := by
    by_cases hη : ∃ z ∈ V.model.filtration.realification.subgroup (k + 1),
        realifyFunctional η z.coord ≠ 0
    · obtain ⟨G, hG⟩ := hstep k hk r (hp.trans hpr) (hCR.trans hpK) V η
        hheight' hvertical hη hV
      exact ⟨{ G with complexity := G.complexity.mono hCR },
        (Real.exp_le_exp.mpr (neg_le_neg hCR)).trans_lt hG⟩
    · have hinv : ∀ z ∈ V.model.filtration.realification.subgroup (k + 1), ∀ x,
          V.test.observable (z • x) = V.test.observable x := by
        intro z hz x
        have hz₀ : realifyFunctional η z.coord = 0 :=
          not_ne_iff.mp fun hne => hη ⟨z, hz, hne⟩
        have hchar : CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) = 1 := by
          rw [hz₀]
          simp
        have hx : V.test.observable (z • x) =
            CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
              V.test.observable x := hvertical z hz x
        rw [hx, hchar, one_mul]
      obtain ⟨G, hG⟩ := hTop k X r (hp₀.trans hpr) V hinv
      let G' : NativePrimeTest k X (p ^ K) := { G with complexity := G.complexity.mono hTopR }
      have heval : G'.eval = V.eval := funext hG
      refine ⟨G', ?_⟩
      rw [heval]
      exact (Real.exp_le_exp.mpr (neg_le_neg (hrC.trans hCR))).trans_lt hV
  exact ⟨G.eval, ⟨G, rfl⟩, hG⟩

end PrimeUniformity

#print axioms PrimeUniformity.native_prime_step_descent_of_vertical
#print axioms PrimeUniformity.nativePrimeTest_select_vertical_at_budget
