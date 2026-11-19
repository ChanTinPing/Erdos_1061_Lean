import UpstreamPrimeRankAdapted
import UpstreamVerticalDescent

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- The remaining rank step acts on a normalized native vertical test with
an adapted basis and its actual Vaughan alternative. -/
def NativePrimePreparedRankStepDescent (S : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ k < S, ∀ r < k + 1, ∀ p : ℝ,
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
      (DenseTypeIPrefixes X X.sqrt A F (Real.exp (-20 * p)) ∨
        ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X,
          (X : ℝ) * Real.exp (-20 * p) < ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖) →
      ∃ G : NativeRankedPrimeTest (k + 1) r X (p ^ C),
        Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval

/-- Normalize, adapt the basis, and select a correlated vertical mode.
The zero top-rank frequency uses the rank quotient directly. -/
theorem native_prime_rank_step_descent_of_prepared {S : ℕ}
    (h : NativePrimePreparedRankStepDescent S) : NativePrimeRankStepDescent S := by
  obtain ⟨C, hC, b, hb, hstep⟩ := h
  obtain ⟨a, _, hFourier⟩ := exists_verticalDecompositionBudget_bound
  choose D hD hnorm using fun k : ℕ => nativeRankedPrimeTest_exists_normalized (k + 1)
  choose E hE hdrop using fun k : ℕ => nativeRankedPrimeTest_rankInvariant_drop (k + 1)
  let M := 2 + ∑ k ∈ Finset.range S, (D k + E k)
  have hM : 2 ≤ M := by dsimp only [M]; omega
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hDE (k : ℕ) (hk : k < S) : D k ≤ M ∧ E k ≤ M := by
    have hsum := Finset.single_le_sum (f := fun k => D k + E k)
      (fun j _ => Nat.zero_le (D j + E j)) (Finset.mem_range.mpr hk)
    dsimp only [M]
    omega
  let Xp : Polynomial ℕ := Polynomial.X
  let Np := (Xp + Polynomial.C M) ^ M
  let Ap := (Np + 3) ^ 11 + Np + 2
  let Tp := Ap + (Ap + 2) ^ 2
  let Vp := 12 * Tp + 2 * Tp + (12 * Tp + Polynomial.C a) ^ a
  let P := Vp ^ C + ((Vp + 3) ^ 11 + Polynomial.C M) ^ M
  obtain ⟨K, hK, hpK⟩ := exists_natPolynomial_eval_le_power P
  obtain ⟨B, hB, hweight⟩ := eventually_abs_strictVonMangoldtCramerDifference
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let b₀ := min b (1 / 20 : ℝ)
  refine ⟨K, hK, b₀, lt_min hb (by norm_num), ?_⟩
  filter_upwards [hstep, hweight, hlog.eventually_ge_atTop B, eventually_gt_atTop (0 : ℕ),
    eventually_nativePrimeTest_vaughan_cases] with X hstep hweight hLB hX hcases
  intro k hk r hr p hp hbudget W hlarge
  let L := Real.log (X : ℝ)
  let w := strictVonMangoldtCramerDifference X
  let N := (p + M) ^ M
  let T := rankAdaptedNiltestBudget N
  let v := 12 * T + 2 * T + (12 * T + a) ^ a
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hN : p ≤ N := (by linarith : p ≤ p + M).trans (by
    simpa only [N, pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + M)
      (show 1 ≤ M by omega))
  have hNT : N ≤ T := le_rankAdaptedNiltestBudget (hp₀.trans hN)
  have hT : p ≤ T := hN.trans hNT
  have hT₀ : 0 ≤ T := hp₀.trans hT
  have hTv : T ≤ v := by
    dsimp only [v]
    exact (show T ≤ 12 * T + 2 * T by linarith).trans (le_add_of_nonneg_right (by positivity))
  have hv : p ≤ v := hT.trans hTv
  have hv₂ : 2 ≤ v := hp₂.trans hv
  have hcost : v ^ C + ((v + 3) ^ (11 : ℕ) + M) ^ M ≤ p ^ K := by
    simpa [P, Vp, Tp, Ap, Np, Xp, v, T, N, rankAdaptedNiltestBudget,
      rankAdaptedNiltestBase, Polynomial.eval₂_pow] using hpK p hp₂
  have hvK : v ^ C ≤ p ^ K := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hL : 1 ≤ L := hB.trans hLB
  have hvb : v ^ C ≤ L ^ b :=
    (hvK.trans hbudget).trans (Real.rpow_le_rpow_of_exponent_le hL (min_le_left _ _))
  have hvX : v ≤ L ^ (1 / 20 : ℝ) := by
    have hvC : v ≤ v ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ v) hC
    exact (hvC.trans (hvK.trans hbudget)).trans
      (Real.rpow_le_rpow_of_exponent_le hL (min_le_right _ _))
  have hDM : (D k : ℝ) ≤ M := by exact_mod_cast (hDE k hk).1
  have hnormN : (p + (D k : ℝ)) ^ (D k) ≤ N :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hDM) _).trans
      (pow_le_pow_right₀ (by linarith) (hDE k hk).1)
  obtain ⟨W₀, hW₀, hzero₀⟩ := hnorm k W hp₀
  let W₁ : NativeRankedPrimeTest (k + 1) (r + 1) X N :=
    ⟨{ W₀.test with complexity := W₀.test.complexity.mono hnormN }, W₀.rank,
      W₀.complexity.mono W₀.rank hnormN⟩
  obtain ⟨U, hU, hzeroU, ω, hω⟩ := nativeRankedPrimeTest_exists_adapted W₁ (hp₀.trans hN)
  have hcU : Real.exp (-T) < intervalCorrelation X w U.test.eval := by
    rw [hU, show W₁.test.eval = W.test.eval from hW₀]
    exact (Real.exp_le_exp.mpr (neg_le_neg hT)).trans_lt hlarge
  have hLe : L ≤ Real.exp p :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans_le hL)).mp ((le_max_right _ _).trans hp)
  have hw (n : ℤ) (hn : n ∈ interval 1 (X : ℤ)) : |w n| ≤ Real.exp (9 * T) := calc
    _ ≤ B * L ^ (8 : ℕ) := hweight n hn
    _ ≤ L ^ (9 : ℕ) := by
      rw [pow_succ' L 8]
      exact mul_le_mul_of_nonneg_right hLB (pow_nonneg (by linarith) 8)
    _ ≤ Real.exp p ^ (9 : ℕ) := pow_le_pow_left₀ (by linarith) hLe 9
    _ = Real.exp (9 * p) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨η, F, hF, hFnorm, hOrbit, hη, hvert, hcV⟩ :=
    nativePrimeTest_select_vertical_at_budget hFourier hX (hp₂.trans hT) U.test w hw hcU
  let V : NativeRankedPrimeTest (k + 1) (r + 1) X v :=
    ⟨{ U.test with test := F, complexity := hF, bound := hFnorm }, U.rank,
      U.complexity.mono U.rank hTv⟩
  have hzeroV : V.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0
      V.test.test.orbit = 1 := by
    change U.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 F.orbit = 1
    rw [hOrbit]
    exact hzeroU hzero₀
  have hcorr : Real.exp (-v) < intervalCorrelation X w V.test.eval := hcV
  apply Or.inl
  by_cases hnonzero : ∃ z ∈ V.rank.realSubgroup (k + 1) (r + 1), realifyFunctional η z.coord ≠ 0
  · obtain ⟨hstride, hcase⟩ := hcases (k + 1) v (hp.trans hv) hvX V.test hcorr
    obtain ⟨G, hG⟩ := hstep k hk r hr v (hp.trans hv) hvb V ω hω hzeroV η hη hvert hnonzero hcorr hstride hcase
    let G' : NativeRankedPrimeTest (k + 1) r X (p ^ K) :=
      ⟨{ G.test with complexity := G.test.complexity.mono hvK }, G.rank, G.complexity.mono G.rank hvK⟩
    exact ⟨G', (Real.exp_le_exp.mpr (neg_le_neg hvK)).trans_lt hG⟩
  · have hinv (z) (hz : z ∈ V.rank.realSubgroup (k + 1) (r + 1)) (x) :
        V.test.test.observable (z • x) = V.test.test.observable x := by
      have hz₀ : realifyFunctional η z.coord = 0 :=
        not_ne_iff.mp fun hne => hnonzero ⟨z, hz, hne⟩
      change F.observable (z • x) = F.observable x
      rw [hvert z (V.rank.realSubgroup_le_degree _ _ hz) x, hz₀]
      simp
    obtain ⟨G, hG⟩ := hdrop k V (hp₀.trans hv) hinv
    let g := ((v + 3) ^ (11 : ℕ) + E k) ^ (E k)
    have hEM : (E k : ℝ) ≤ M := by exact_mod_cast (hDE k hk).2
    have hstart : 1 ≤ (v + 3) ^ (11 : ℕ) + (M : ℝ) := by
      linarith [show 0 ≤ (v + 3) ^ (11 : ℕ) by positivity]
    have hgK : g ≤ p ^ K := by
      calc
        _ ≤ ((v + 3) ^ (11 : ℕ) + M) ^ (E k) :=
          pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hEM) _
        _ ≤ ((v + 3) ^ (11 : ℕ) + M) ^ M := pow_le_pow_right₀ hstart (hDE k hk).2
        _ ≤ _ := (le_add_of_nonneg_left (by positivity)).trans hcost
    have hvG : v ≤ g := (by linarith : v ≤ v + 3).trans (by
      have h₁ : 1 ≤ v + 3 := by linarith
      have h₁₁ : v + 3 ≤ (v + 3) ^ (11 : ℕ) := by
        simpa only [pow_one] using pow_le_pow_right₀ h₁ (by decide : (1 : ℕ) ≤ 11)
      have hE' : (0 : ℝ) ≤ E k := Nat.cast_nonneg _
      have hb₁ : 1 ≤ (v + 3) ^ (11 : ℕ) + E k := by linarith
      exact (h₁₁.trans (le_add_of_nonneg_right hE')).trans (by
        simpa only [g, pow_one] using pow_le_pow_right₀ hb₁ (show 1 ≤ E k by have := hE k; omega)))
    let G' : NativeRankedPrimeTest (k + 1) r X (p ^ K) :=
      ⟨{ G.test with complexity := G.test.complexity.mono hgK }, G.rank, G.complexity.mono G.rank hgK⟩
    refine ⟨G', ?_⟩
    change Real.exp (-(p ^ K)) < intervalCorrelation X w G.test.eval
    rw [hG]
    exact (Real.exp_le_exp.mpr (neg_le_neg (hvG.trans hgK))).trans_lt hcorr

end PrimeUniformity

#print axioms PrimeUniformity.native_prime_rank_step_descent_of_prepared
