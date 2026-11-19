import UpstreamRankedDescentCorrelation
import PrimeUniformity.UpstreamInverseReduction

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- A positive integer block length controls both the freezing error and
the number of interval blocks. -/
theorem exists_ranked_freezing_partition {X : ℕ} (hX : 0 < X) {p a : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hsize : a + 10 * p + 3 ≤ Real.log (X : ℝ)) :
    let d := a + 10 * p + 2
    ∃ B : ℕ, 0 < B ∧
      Real.exp a * ((B : ℝ) / (X : ℝ)) * Real.exp (9 * p) ≤ Real.exp (-p - 2) ∧
      ∀ n ≤ X, (↑(n / B + 1) : ℝ) ≤ Real.exp (d + 2) := by
  intro d
  let Y := (X : ℝ) * Real.exp (-d)
  let B := ⌊Y⌋₊
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hdX : d + 1 ≤ Real.log (X : ℝ) := by dsimp only [d]; linarith
  have hY : 2 ≤ Y := calc
    _ ≤ Real.exp 1 := (by norm_num : (2 : ℝ) ≤ 1 + 1).trans (Real.add_one_le_exp 1)
    _ ≤ Real.exp (Real.log (X : ℝ) - d) := Real.exp_le_exp.mpr (by linarith)
    _ = Y := by rw [Real.exp_sub, Real.exp_log hX', div_eq_mul_inv, ← Real.exp_neg]
  have hB : 0 < B := by
    change 1 ≤ ⌊Y⌋₊
    apply Nat.le_floor
    rw [Nat.cast_one]
    linarith
  have hB' : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hBY : (B : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYB : Y / 2 ≤ (B : ℝ) := by
    have h := Nat.lt_floor_add_one Y
    change Y < (B : ℝ) + 1 at h
    linarith
  have hfrac : (B : ℝ) / X ≤ Real.exp (-d) := (div_le_iff₀ hX').mpr (by
    rw [mul_comm]
    exact hBY)
  have hInv : (X : ℝ) / B ≤ 2 * Real.exp d := by
    apply (div_le_iff₀ hB').mpr
    calc
      _ = (2 * Real.exp d) * (Y / 2) := by
        dsimp only [Y]
        calc
          _ = (X : ℝ) * (Real.exp d * Real.exp (-d)) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hYB (by positivity)
  refine ⟨B, hB, ?_, ?_⟩
  · calc
      _ ≤ Real.exp a * Real.exp (-d) * Real.exp (9 * p) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [d]
        ring
  · intro n hn
    have hdiv : ((n / B : ℕ) : ℝ) ≤ (X : ℝ) / B := by
      apply (le_div_iff₀ hB').mpr
      exact_mod_cast (Nat.div_mul_le_self n B).trans hn
    calc
      _ ≤ 2 * Real.exp d + 1 := by
        push_cast
        linarith only [hdiv, hInv]
      _ ≤ 3 * Real.exp d := by linarith [Real.one_le_exp hd]
      _ ≤ Real.exp 2 * Real.exp d :=
        mul_le_mul_of_nonneg_right ((by norm_num : (3 : ℝ) ≤ 2 + 1).trans (Real.add_one_le_exp 2))
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem freezing_natPolynomial_le_power (P : Polynomial ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℝ, 2 ≤ p → P.eval₂ (Nat.castRingHom ℝ) p ≤ p ^ A := by
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

/-- Once the normalized factors and the lifted middle orbit are supplied,
the strict prime–Cramér correlation survives one rank drop. -/
theorem nativeRankedPrimeTest_rank_drop_of_normalized_factors (s k : ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ᶠ X : ℕ in atTop,
      ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        {d r : ℕ} {p : ℝ},
        max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ A ≤ Real.log (X : ℝ) →
        ∀ (Z : NativeRankedPrimeTest s (r + 1) X p),
        let W := Z.test
        (W.q : ℝ) ≤ Real.exp (11 * p) →
        ∀ (D : RationalFilteredNilmanifold L s d) (RD : D.DegreeRankStructure (r + 1)),
        RD.ComplexityLE p →
        ∀ (φ : L →ₗ⁅ℚ⁆ W.L),
        (∀ i j, rationalLogHeight (W.model.basis.repr (φ (D.basis j)) i) ≤ p) →
        ∀ (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (η : W.L →ₗ[ℚ] ℚ),
        (∀ z ∈ Z.rank.realSubgroup s (r + 1), ∀ x,
          W.test.observable (z • x) =
            CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
              W.test.observable x) →
        ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        ∀ (E m R : (W.model.filtration.realification.adaptedPolynomialFiltration
          (fun _ : Unit => 1)).Group) (κ : W.model.RealGroup),
        κ ∈ W.model.realLattice →
        E * m * R * W.model.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ =
          ⟨⟨W.test.orbit.log, W.test.orbit.property⟩⟩ →
        W.model.filtration.PolynomialRationalGrid W.model.basis (fun _ => 1) q R →
        W.model.filtration.PolynomialSlowBound W.model.basis (fun _ => 1)
          (fun _ => (X : ℝ)) (Real.exp ((p + 2) ^ k)) E →
        let Φ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := W.model.filtration.lowerCentralSeries_eq_bot) φ
        (∀ n : ℤ, Φ (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) =
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (n : ℝ)) m) →
        (∀ z ∈ RD.realSubgroup s (r + 1),
          Φ z ∈ Z.rank.realSubgroup s (r + 1) ∧ realifyFunctional η (Φ z).coord = 0) →
        Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.eval →
        ∃ G : NativeRankedPrimeTest s r X (p ^ A),
          Real.exp (-(p ^ A)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval := by
  obtain ⟨C, K, _, _, hfreeze⟩ := nativeRankedPrimeTest_corr_of_normalized_factors s k
  obtain ⟨J, _, hdrop⟩ := nativeRankedPrimeTest_rankInvariant_drop s
  let T : Polynomial ℕ := Polynomial.X
  let H := (T + 2) ^ C
  let D₀ := H + 10 * T + 2
  let N := 11 * T + H + (D₀ + 2)
  let Q := (((T + Polynomial.C K) ^ K + 3) ^ 11 + Polynomial.C J) ^ J
  obtain ⟨A, hA, hbudget⟩ := freezing_natPolynomial_le_power ((D₀ + 1) + (T + N + 2) + Q)
  obtain ⟨M₀, hM₀, hpoint⟩ := eventually_abs_strictVonMangoldtCramerDifference
  have htend : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨A, hA, ?_⟩
  filter_upwards [hpoint, htend.eventually_ge_atTop M₀, eventually_gt_atTop (0 : ℕ)] with X hpoint hXM hX
  intro L _ _ _ _ _ _ d r p hp hpX Z W hWq D RD hRD φ hφ g η hvertical q hq hqp E m R κ hκ hprod
    hgrid hslow Φ hfast htop hlarge
  let w := strictVonMangoldtCramerDifference X
  change Real.exp (-p) < intervalCorrelation X w W.eval at hlarge
  let a := (p + 2) ^ C
  let d₀ := a + 10 * p + 2
  let τ := 11 * p + a + (d₀ + 2)
  let u := (p + K) ^ K
  let v := ((u + 3) ^ (11 : ℕ) + J) ^ J
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₁ : 1 ≤ p := by linarith
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hd₀ : 0 ≤ d₀ + 1 := by dsimp only [d₀]; positivity
  have hτ : 0 ≤ p + τ + 2 := by dsimp only [τ, d₀]; positivity
  have hv : 0 ≤ v := by dsimp only [v, u]; positivity
  have hbudget' : d₀ + 1 + (p + τ + 2) + v ≤ p ^ A := by
    simpa [D₀, H, N, T, Q, a, d₀, τ, u, v, Polynomial.eval₂_pow] using hbudget p hp₂
  have hdX : a + 10 * p + 3 ≤ Real.log (X : ℝ) := by
    have hda : d₀ + 1 ≤ p ^ A := by linarith only [hbudget', hτ, hv]
    dsimp only [d₀] at hda
    linarith only [hda, hpX]
  have hτA : p + τ + 2 ≤ p ^ A := by linarith only [hbudget', hd₀, hv]
  have hvA : v ≤ p ^ A := by linarith only [hbudget', hd₀, hτ]
  obtain ⟨B, hB, hErr, hblocks⟩ := exists_ranked_freezing_partition hX (by linarith : 0 ≤ p) ha hdX
  let I := (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val)
  have hI : I ⊆ Finset.Ioc 0 X := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt hlo, hhi.trans W.endpoints.2.1⟩
  have hcard : (I.card : ℝ) ≤ X := by
    exact_mod_cast (show I.card ≤ X by
      simpa using Finset.card_le_card hI)
  have hlog : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le (hM₀.trans hXM)
  have hlogexp : Real.log (X : ℝ) ≤ Real.exp p :=
    (Real.log_le_iff_le_exp hlog).mp ((le_max_right _ _).trans hp)
  have hweight (n : ℕ) (hn : n ∈ I) : |w (n : ℤ)| ≤ Real.exp (9 * p) := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (hI hn)
    have hlo' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hlo
    have hhi' : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hhi
    have hn' : (n : ℤ) ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ)) :=
      Finset.mem_Ico.mpr ⟨hlo', by omega⟩
    calc
      _ ≤ M₀ * Real.log (X : ℝ) ^ (8 : ℕ) := hpoint _ hn'
      _ ≤ Real.log (X : ℝ) ^ (9 : ℕ) := by
        rw [pow_succ' _ 8]
        exact mul_le_mul_of_nonneg_right hXM (by positivity)
      _ ≤ Real.exp p ^ (9 : ℕ) := pow_le_pow_left₀ hlog.le hlogexp 9
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hmass : (∑ n ∈ I, |w (n : ℤ)|) ≤ (X : ℝ) * Real.exp (9 * p) := calc
    _ ≤ ∑ _n ∈ I, Real.exp (9 * p) := Finset.sum_le_sum hweight
    _ = (I.card : ℝ) * Real.exp (9 * p) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
  have hhalf : 2 * Real.exp (-p - 2) ≤ Real.exp (-p) := calc
    _ ≤ Real.exp 2 * Real.exp (-p - 2) :=
      mul_le_mul_of_nonneg_right ((by norm_num : (2 : ℝ) ≤ 2 + 1).trans (Real.add_one_le_exp 2))
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp a * ((B : ℝ) / X) * Real.exp (9 * p) < intervalCorrelation X w W.eval := by
    linarith only [hErr, hhalf, hlarge, Real.exp_pos (-p - 2)]
  obtain ⟨P, _, hP, G, hGinv, hcorr⟩ := hfreeze hX hp₁ Z D RD hRD φ hφ g η hvertical
    q hq hqp E m R κ hκ hprod hgrid hslow hfast htop w (Real.exp (9 * p)) B hB hmass hsmall
  let c : ℝ := ↑((W.q * P) * ((W.V - W.U) / B + 1))
  change intervalCorrelation X w W.eval ≤ Real.exp a * ((B : ℝ) / X) * Real.exp (9 * p) +
    c * intervalCorrelation X w G.test.eval at hcorr
  have hcells : c ≤ Real.exp τ := by
    have hblock := hblocks (W.V - W.U) ((Nat.sub_le _ _).trans W.endpoints.2.1)
    calc
      _ ≤ Real.exp (11 * p) * Real.exp a * Real.exp (d₀ + 2) := by
        simp only [c, Nat.cast_mul]
        exact mul_le_mul (mul_le_mul hWq hP (Nat.cast_nonneg _) (Real.exp_nonneg _)) hblock
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hretained : Real.exp (-(p ^ A)) < intervalCorrelation X w G.test.eval := by
    by_contra! hG
    have hpτ : Real.exp τ * Real.exp (-(p ^ A)) ≤ Real.exp (-p - 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hτA])
    have hnonneg : 0 ≤ intervalCorrelation X w G.test.eval := by
      unfold intervalCorrelation
      exact norm_nonneg _
    have hprodG : c * intervalCorrelation X w G.test.eval ≤ Real.exp (-p - 2) :=
      (mul_le_mul hcells hG hnonneg (Real.exp_pos _).le).trans hpτ
    linarith only [hcorr, hErr, hprodG, hhalf, hlarge]
  obtain ⟨G₀, hG₀⟩ := hdrop G (by positivity) hGinv
  let G' : NativeRankedPrimeTest s r X (p ^ A) :=
    ⟨{ G₀.test with complexity := G₀.test.complexity.mono hvA }, G₀.rank, G₀.complexity.mono G₀.rank hvA⟩
  have hEval : G'.test.eval = G.test.eval := hG₀
  exact ⟨G', by rw [hEval]; exact hretained⟩

end PrimeUniformity
