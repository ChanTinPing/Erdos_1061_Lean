import UpstreamDescentCorrelation
import UpstreamPrimeRankIteration
import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- Realize a frozen observable on the source orbit and a refined
progression while retaining the source degree-rank structure. -/
theorem nativeRankedPrimeTest_of_frozen_orbit (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r X : ℕ} {p : ℝ} (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (W : NativePrimeTest s X p) (φ : L →ₗ⁅ℚ⁆ W.L)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → R.ComplexityLE p →
      (∀ i j, rationalLogHeight (W.model.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ ε γ : W.model.RealGroup,
        (∀ i, |(W.model.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (W.model.basis.baseChange ℝ).equivFun γ.coord ∈ realDenominatorGrid q →
        let frozen (x : D.RealGroup) := W.test.observable (QuotientGroup.mk
          (ε * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := W.model.filtration.lowerCentralSeries_eq_bot) φ x * γ))
        (∀ z ∈ R.realSubgroup s r, ∀ x : D.RealGroup, frozen (z * x) = frozen x) →
        ∀ a b m : ℕ, a ≤ b → b ≤ X → 0 < m → ∀ c : ZMod m,
          ∃ G : NativeRankedPrimeTest s r X ((p + C) ^ C),
            (∀ n : ℤ, G.test.eval n = if n ∈ residueSlice ((a : ℤ) + 1) ((b - a : ℕ) : ℤ) c then
              frozen (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) else 0) ∧
            (∀ z ∈ G.rank.realSubgroup s r, ∀ x,
              G.test.test.observable (z • x) = G.test.test.observable x) := by
  obtain ⟨A, _, hmaps⟩ := exists_uniform_frozen_map s k
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C A) ^ A + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d r X p D R W φ g hp hR hφ q hq hqp ε γ hε hγ frozen hinv a b m hab hbX hm c
  obtain ⟨Λ, _, _, _, _, _, N, hN, hin, hout, hF, hmap⟩ :=
    hmaps D W.model φ p hp hR.1 W.complexity.1 hφ q hq hqp
  obtain ⟨hconj, K, hK, hKlip⟩ := hmap ε γ hε hγ
  let F := D.withLattice Λ N hN hin hout
  let RF := R.withLattice Λ N hN hin hout
  let T := F.frozenComplexNiltest W.model φ ε γ hconj W.test g K hKlip
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hcap : p + u + 4 ≤ (p + C) ^ C := by
    simpa [Q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := (by linarith : p ≤ p + u + 4).trans hcap
  have huC : u ≤ (p + C) ^ C := (by linarith : u ≤ p + u + 4).trans hcap
  have hT : T.ComplexityLE ((p + C) ^ C) :=
    (F.frozenComplexNiltest_complexity W.model φ ε γ hconj W.test g K hKlip
      hp hu hF W.complexity hK).mono hcap
  have hRF : RF.ComplexityLE ((p + C) ^ C) :=
    R.withLattice_complexity Λ N hN hin hout hR hpC (hF.mono F huC)
  let G : NativeRankedPrimeTest s r X ((p + C) ^ C) :=
    { test := {
        L := L
        dim := d
        model := F
        test := T
        complexity := hT
        bound := W.bound
        U := a
        V := b
        q := m
        a := c
        endpoints := ⟨hab, hbX, hm⟩ }
      rank := RF
      complexity := hRF }
  refine ⟨G, ?_, ?_⟩
  · intro n
    rfl
  · intro z hz x
    induction x using Quotient.inductionOn with
    | h x => exact hinv z hz x

/-- Freeze the normalized outer factors and retain one refined progression
on a ranked test whose observable is invariant under its top rank. -/
theorem nativeRankedPrimeTest_corr_of_normalized_factors (s k : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧
      ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        {d r X : ℕ} {p : ℝ} (hX : 0 < X) (hp : 1 ≤ p)
        (Z : NativeRankedPrimeTest s r X p),
        let W := Z.test
        ∀ (D : RationalFilteredNilmanifold L s d) (RD : D.DegreeRankStructure r),
        RD.ComplexityLE p →
        ∀ (φ : L →ₗ⁅ℚ⁆ W.L),
        (∀ i j, rationalLogHeight (W.model.basis.repr (φ (D.basis j)) i) ≤ p) →
        ∀ (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (η : W.L →ₗ[ℚ] ℚ),
        (∀ z ∈ Z.rank.realSubgroup s r, ∀ x,
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
        (∀ z ∈ RD.realSubgroup s r,
          Φ z ∈ Z.rank.realSubgroup s r ∧ realifyFunctional η (Φ z).coord = 0) →
        ∀ (w : ℤ → ℝ) (M : ℝ) (B : ℕ), 0 < B →
        (∑ n ∈ (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val),
          |w (n : ℤ)|) ≤ (X : ℝ) * M →
        let ε := Real.exp ((p + 2) ^ C) * ((B : ℝ) / (X : ℝ))
        ε * M < intervalCorrelation X w W.eval →
        ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          ∃ G : NativeRankedPrimeTest s r X ((p + K) ^ K),
            (∀ z ∈ G.rank.realSubgroup s r, ∀ x, G.test.test.observable (z • x) = G.test.test.observable x) ∧
            intervalCorrelation X w W.eval ≤ ε * M +
              (↑((W.q * P) * ((W.V - W.U) / B + 1)) : ℝ) * intervalCorrelation X w G.test.eval := by
  obtain ⟨C, hC, hFreeze⟩ := RationalFilteredNilmanifold.Niltest.exists_anchored_factor_freezing s k
  obtain ⟨K, hK, hBuild⟩ := nativeRankedPrimeTest_of_frozen_orbit s C
  refine ⟨C, K, hC, hK, ?_⟩
  intro L _ _ _ _ _ _ d r X p hX hp Z W D RD hRD φ hφ g η hvertical q hq hqp E m R κ hκ hprod
    hgrid hslow Φ hfast htop w M B hB hw ε hlarge
  have hp₀ : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hσ : (Fintype.card Unit : ℝ) ≤ p := by simpa using hp
  obtain ⟨P, hP, hPbound, hanchored⟩ := hFreeze W.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) p hp₀ W.complexity.1 hσ q hq hqp
  let left (z : ℕ) := W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (z : ℝ)) E
  let right (z : ℕ) := W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (z : ℝ)) R
  let frozen (z : ℕ) (n : ℤ) := W.test.observable (QuotientGroup.mk
    (left z * Φ (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) * right z))
  let A := (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val)
  have hAX (n : ℕ) (hn : n ∈ A) : n ≤ X :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2.trans W.endpoints.2.1
  have hIntAbs (n : ℕ) (hnX : n ≤ X) : |((n : ℤ) : ℝ)| ≤ (X : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    exact_mod_cast hnX
  have hdata (z : ℕ) (hz : z ∈ A) := hanchored W.test W.complexity E m R κ hκ hprod hgrid
    (fun _ => (X : ℝ)) (fun _ => hX') hslow (fun _ => (z : ℤ))
    (fun _ => hIntAbs z (hAX z hz))
  have hfreeze (n : ℕ) (hn : n ∈ A) (z : ℕ) (hz : z ∈ A)
      (hmod : n % P = z % P) (hclose : |(n : ℝ) - (z : ℝ)| ≤ (B : ℝ)) :
      ‖W.test.eval (fun _ => (n : ℤ)) - frozen z (n : ℤ)‖ ≤ ε := by
    have hdvd : (P : ℤ) ∣ (n : ℤ) - (z : ℤ) := (show Nat.ModEq P z n from hmod.symm).dvd
    let δ := (B : ℝ) / (X : ℝ)
    have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg B) hX'.le
    have hscale : (X : ℝ) * δ = (B : ℝ) := by
      dsimp only [δ]
      rw [mul_comm, div_mul_cancel₀ _ hX'.ne']
    have hclose' : |((n : ℤ) : ℝ) - ((z : ℤ) : ℝ)| ≤ (X : ℝ) * δ := by
      simpa only [Int.cast_natCast, hscale] using hclose
    have he := (hdata z hz).2.2 (fun _ => (n : ℤ)) δ hδ (fun _ => hIntAbs n (hAX n hn))
      (fun _ => hdvd) (fun _ => hclose')
    simpa only [frozen, left, right, hfast, Int.cast_natCast] using he
  have hqW : 0 < W.q := W.endpoints.2.2
  let : NeZero W.q := ⟨hqW.ne'⟩
  have hrW : W.a.val < W.q := ZMod.val_lt W.a
  have hOrig (n : ℤ) : (if n ∈ residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ)
      (W.a.val : ZMod W.q) then W.test.eval (fun _ => n) else 0) = W.eval n := by
    simp only [ZMod.natCast_zmod_val, NativePrimeTest.eval]
  obtain ⟨z, hz, a, b, c, hab, hbX, hc, hcorr⟩ := exists_frozen_progression_correlation
    hX W.endpoints.1 W.endpoints.2.1 hrW hP hB w (fun n => W.test.eval (fun _ => n)) frozen
      (by positivity : 0 ≤ ε) hw hfreeze (by simpa only [hOrig] using hlarge)
  have hfrozen (z' : D.RealGroup) (hz' : z' ∈ RD.realSubgroup s r) (x : D.RealGroup) :
      W.test.observable (QuotientGroup.mk (left z * Φ (z' * x) * right z)) =
        W.test.observable (QuotientGroup.mk (left z * Φ x * right z)) := by
    obtain ⟨hmem, hzero⟩ := htop z' hz'
    have hcomm := Z.rank.top_realSubgroup_commute hmem (left z)
    have hmul : left z * Φ (z' * x) * right z = Φ z' * (left z * Φ x * right z) := by
      rw [map_mul, ← mul_assoc (left z) (Φ z') (Φ x), hcomm.eq.symm]
      simp only [mul_assoc]
    rw [hmul]
    change W.test.observable (Φ z' • (QuotientGroup.mk (left z * Φ x * right z) : W.model.Space)) = _
    rw [hvertical _ hmem, hzero]
    simp
  obtain ⟨G, hG, hGinv⟩ := hBuild D RD W φ g hp₀ hRD hφ q hq hqp (left z) (right z)
    (by simpa only [left, Int.cast_natCast] using (hdata z hz).1)
    (by simpa only [right, Int.cast_natCast] using (hdata z hz).2.1)
    hfrozen a b (W.q * P) hab hbX (Nat.mul_pos hqW hP) (c : ZMod (W.q * P))
  have hEval : G.test.eval = fun n => if n ∈ residueSlice ((a : ℤ) + 1)
      ((b - a : ℕ) : ℤ) (c : ZMod (W.q * P)) then frozen z n else 0 := funext hG
  exact ⟨P, hP, hPbound, G, hGinv, by simpa only [hOrig, ← hEval] using hcorr⟩

end PrimeUniformity
