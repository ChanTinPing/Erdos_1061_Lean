import PrimeUniformity.CorrelationDescent
import PrimeUniformity.UpstreamIntervalNorm
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse
import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent
import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace PrimeUniformity

open OAI.Erdos3
open Module
open NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

structure NativePrimeTest (s X : ℕ) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  test : model.Niltest (fun _ : Unit => 1)
  complexity : test.ComplexityLE p
  bound : test.normBound ≤ 1
  U : ℕ
  V : ℕ
  q : ℕ
  a : ZMod q
  endpoints : U ≤ V ∧ V ≤ X ∧ 0 < q

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

noncomputable def NativePrimeTest.eval {s X : ℕ} {p : ℝ} (W : NativePrimeTest s X p) (n : ℤ) : ℂ :=
  if n ∈ residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ) W.a
  then W.test.eval (fun _ => n) else 0

def nativePrimeTests (s X : ℕ) (p : ℝ) : Set (ℤ → ℂ) :=
  {F | ∃ W : NativePrimeTest s X p, F = W.eval}

theorem nativePrimeTests_mono (s X : ℕ) : Monotone (nativePrimeTests s X) := by
  intro p q hpq F hF
  obtain ⟨W, rfl⟩ := hF
  exact ⟨{ W with complexity := W.complexity.mono hpq }, rfl⟩

theorem nativePrimeTests_zero (X : ℕ) (p : ℝ) :
    nativePrimeTests 0 X p ⊆ ProgressionCombination X p := by
  intro F hF
  obtain ⟨W, rfl⟩ := hF
  let z := W.test.eval (fun _ => 0)
  have hz := W.test.eval_budget W.complexity (fun _ => 0)
  refine ⟨1, fun _ => W.U, fun _ => W.V, fun _ => W.q, fun _ => W.a, fun _ => z,
    fun _ => W.endpoints, ?_, ?_⟩
  · simpa [z] using hz
  · ext n
    simp only [NativePrimeTest.eval, Fin.sum_univ_one]
    congr 1
    simp only [z, RationalFilteredNilmanifold.Niltest.eval_step_zero]

theorem nativePrimeTests_inverse {s : ℕ} (hs : 1 ≤ s) :
    IntervalCorrelationInverse s.succ (nativePrimeTests s) := by
  obtain ⟨C, hC, hinverse⟩ := exists_native_integer_interval_inverse s hs
  refine ⟨C, hC, ?_⟩
  intro X hX p hp w hw hgowers
  letI : NeZero X := ⟨hX.ne'⟩
  have hcomplex (n : ℤ) (hn : n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ))) :
      ‖(w n : ℂ)‖ ≤ 1 := by
    simpa using hw n hn
  rw [intervalGowersNorm_eq_upstream] at hgowers
  obtain ⟨V, hV⟩ := hinverse 1 X hp (fun n => (w n : ℂ)) hcomplex hgowers
  let W : NativePrimeTest s X ((p + C) ^ C) :=
    { L := V.L, dim := V.dim, model := V.model, test := V.test, complexity := V.complexity, bound := hV
      U := 0, V := X, q := 1, a := 0, endpoints := ⟨Nat.zero_le _, le_rfl, Nat.zero_lt_one⟩ }
  refine ⟨W.eval, ⟨W, rfl⟩, ?_⟩
  unfold intervalCorrelation
  refine V.correlation.trans_eq (congrArg norm ?_)
  apply Finset.expect_congr rfl
  intro n hn
  have hn' : n ∈ residueSlice 1 (X : ℤ) (0 : ZMod 1) := by
    exact Finset.mem_filter.mpr ⟨hn, Subsingleton.elim _ _⟩
  have heq : W.eval n = V.test.eval (fun _ => n) := by
    simpa [NativePrimeTest.eval, W, hn']
  rw [heq]

/-- A top-invariant observable descends exactly to the next lower step,
with the same progression support and a polynomial logarithmic budget. -/
theorem nativePrimeTest_topInvariant_drop (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : ℕ) (p : ℝ), 0 ≤ p →
      ∀ W : NativePrimeTest (s + 1) X p,
        (∀ z ∈ W.model.filtration.realification.subgroup (s + 1), ∀ x,
          W.test.observable (z • x) = W.test.observable x) →
        ∃ G : NativePrimeTest s X (((p + 3) ^ (11 : ℕ) + C) ^ C), ∀ n, G.eval n = W.eval n := by
  obtain ⟨C, hC, hdrop⟩ := RationalFilteredNilmanifold.exists_topInvariant_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro X p hp W hinv
  let P := (p + 3) ^ (11 : ℕ)
  obtain ⟨n, _, Q, hQF, hQL, hQg, hQproj, _⟩ :=
    W.model.exists_controlled_top_quotient hp W.complexity.1
  let : TopologicalSpace (ℝ ⊗[ℚ] (W.L ⧸ W.model.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (W.L ⧸ W.model.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (W.L ⧸ W.model.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  have hp3 : 1 ≤ p + 3 := by linarith
  have hpP : p ≤ P := by
    calc
      _ ≤ p + 3 := by linarith
      _ ≤ P := by
        simpa only [pow_one] using pow_le_pow_right₀ hp3 (by decide : (1 : ℕ) ≤ 11)
  have h5 : (p + 3) ^ (5 : ℕ) ≤ P := pow_le_pow_right₀ hp3 (by decide)
  obtain ⟨S, _, hSnorm, hScomplexity, hSeval⟩ :=
    hdrop W.model Q hQF hQL W.test P (hp.trans hpP) (W.complexity.mono hpP) hQg
      (fun i j => (hQproj j i).trans h5) hinv
  let G : NativePrimeTest s X ((P + C) ^ C) :=
    { L := W.L ⧸ W.model.filtration.layerIdeal (s + 1)
      dim := n
      model := Q
      test := S
      complexity := hScomplexity
      bound := by rw [hSnorm]; exact W.bound
      U := W.U
      V := W.V
      q := W.q
      a := W.a
      endpoints := W.endpoints }
  exact ⟨G, fun n => by simp [G, NativePrimeTest.eval, hSeval]⟩

/-- Replace the observable while keeping the model, progression and budget. -/
def NativePrimeTest.withNiltest {s X : ℕ} {p : ℝ} (W : NativePrimeTest s X p)
    (T : W.model.Niltest (fun _ : Unit => 1)) (hT : T.ComplexityLE p) (hB : T.normBound ≤ 1) :
    NativePrimeTest s X p :=
  { W with test := T, complexity := hT, bound := hB }

/-- Select a vertical mode carrying the weighted correlation on the same
orbit, with the Fourier approximation loss and mode count made explicit. -/
theorem nativePrimeTest_correlating_vertical_component_with_orbit {s X : ℕ} {p : ℝ}
    (hX : 0 < X) (hp : 0 ≤ p) (W : NativePrimeTest s X p)
    (w : ℤ → ℝ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) (hρp : ρ⁻¹ ≤ Real.exp p)
    (hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ B)
    (hlarge : B * ρ < intervalCorrelation X w W.eval) :
    ∃ η : W.L →ₗ[ℚ] ℚ, ∃ T : W.model.Niltest (fun _ : Unit => 1),
      ∃ hT : T.ComplexityLE p, ∃ hTbound : T.normBound ≤ 1,
      T.orbit = W.test.orbit ∧
      (∀ i, rationalLogHeight (η (W.model.basis i)) ≤ verticalDecompositionBudget p) ∧
        (∀ z ∈ W.model.filtration.realification.subgroup s, ∀ x,
          T.observable (z • x) = CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) ∧
        intervalCorrelation X w W.eval ≤ B * ρ + Real.exp (verticalDecompositionBudget p) *
          intervalCorrelation X w (W.withNiltest T hT hTbound).eval := by
  classical
  obtain ⟨J, inst, η, T, hJ, hheight, hT, hvert, _, _, herr⟩ :=
    W.test.exists_vertical_decomposition_preserving_bounds hp W.complexity hρ hρp
  letI := inst
  have hbound (j : J) : (T j).normBound ≤ 1 := by rw [(hT j).2.2.1]; exact W.bound
  let G (j : J) := (W.withNiltest (T j) (hT j).1 (hbound j)).eval
  let P := residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ) W.a
  have happrox (n : ℤ) (_ : n ∈ interval 1 (X : ℤ)) :
      ‖W.eval n - ∑ j ∈ Finset.univ, G j n‖ ≤ ρ := by
    by_cases hn : n ∈ P
    · rw [norm_sub_rev]
      change n ∈ residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ) W.a at hn
      simpa [G, NativePrimeTest.eval, NativePrimeTest.withNiltest, hn] using herr (fun _ => n)
    · simp [G, NativePrimeTest.eval, NativePrimeTest.withNiltest, P, hn, hρ.le]
  obtain ⟨j, _, hj⟩ := exists_large_intervalCorrelation_component hX Finset.univ w W.eval G
    hB hw happrox hlarge
  refine ⟨η j, T j, (hT j).1, hbound j, (hT j).2.1, hheight j, hvert j, hj.trans ?_⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (by simpa only [Finset.card_univ] using hJ) (norm_nonneg _))

/-- The selected vertical component retains the weighted correlation with
the stated approximation and counting losses. -/
theorem nativePrimeTest_correlating_vertical_component {s X : ℕ} {p : ℝ}
    (hX : 0 < X) (hp : 0 ≤ p) (W : NativePrimeTest s X p)
    (w : ℤ → ℝ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) (hρp : ρ⁻¹ ≤ Real.exp p)
    (hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ B)
    (hlarge : B * ρ < intervalCorrelation X w W.eval) :
    ∃ η : W.L →ₗ[ℚ] ℚ, ∃ T : W.model.Niltest (fun _ : Unit => 1),
      ∃ hT : T.ComplexityLE p, ∃ hTbound : T.normBound ≤ 1,
      (∀ i, rationalLogHeight (η (W.model.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ W.model.filtration.realification.subgroup s, ∀ x,
        T.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) ∧
      intervalCorrelation X w W.eval ≤ B * ρ + Real.exp (verticalDecompositionBudget p) *
        intervalCorrelation X w (W.withNiltest T hT hTbound).eval := by
  obtain ⟨η, T, hT, hTbound, _, hheight, hvertical, hcorr⟩ :=
    nativePrimeTest_correlating_vertical_component_with_orbit hX hp W w hB hρ hρp hw hlarge
  exact ⟨η, T, hT, hTbound, hheight, hvertical, hcorr⟩

/-- Package a frozen fast orbit as a lower-step native test on the
progression retained by the correlation argument. -/
theorem nativePrimeTest_of_frozen_orbit (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d X : ℕ} {p : ℝ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (W : NativePrimeTest (s + 1) X p) (φ : L →ₗ⁅ℚ⁆ W.L)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (W.model.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ ε γ : W.model.RealGroup,
        (∀ i, |(W.model.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (W.model.basis.baseChange ℝ).equivFun γ.coord ∈ realDenominatorGrid q →
        let frozen (x : D.RealGroup) := W.test.observable (QuotientGroup.mk
          (ε * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := W.model.filtration.lowerCentralSeries_eq_bot) φ x * γ))
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
          frozen (z * x) = frozen x) →
        ∀ a b m : ℕ, a ≤ b → b ≤ X → 0 < m → ∀ r : ZMod m,
          ∃ G : NativePrimeTest s X ((p + C) ^ C), ∀ n : ℤ,
            G.eval n = if n ∈ residueSlice ((a : ℤ) + 1) ((b - a : ℕ) : ℤ) r then
              frozen (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) else 0 := by
  obtain ⟨C, hC, hbuild⟩ := RationalFilteredNilmanifold.exists_uniform_frozen_descent s k
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d X p D W φ g hp hD hφ q hq hqp ε γ hε hγ frozen hinv a b m hab hbX hm r
  obtain ⟨Λ, hΛ, hΛch, hΛN, hΛF, hΛidx, n, _, Q, _, _, _, hdesc⟩ :=
    hbuild D W.model φ W.test g hp hD W.complexity hφ q hq hqp
  let : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, hSnorm, hScomplexity, hSeval⟩ := hdesc ε γ hε hγ hinv
  let G : NativePrimeTest s X ((p + C) ^ C) :=
    { L := L ⧸ D.filtration.layerIdeal (s + 1)
      dim := n
      model := Q
      test := S
      complexity := hScomplexity
      bound := by rw [hSnorm]; exact W.bound
      U := a
      V := b
      q := m
      a := r
      endpoints := ⟨hab, hbX, hm⟩ }
  exact ⟨G, fun n => by simp [G, NativePrimeTest.eval, hSeval, frozen]⟩

/-- The native fifth-order inverse theorem discharges the inverse premise of
the fixed Gowers estimate. -/
theorem gowersUniformityEstimate_of_native_prime_descent
    (hprime : UniformPrimePrefixEstimate)
    (hdescent : PrimeCramerStepDescent 4 nativePrimeTests) :
    GowersUniformityEstimate 5 1280 :=
  gowersUniformityEstimate_of_inverse_and_correlation 4 1280 (nativePrimeTests 4)
    (nativePrimeTests_inverse (by decide))
    (eventually_prime_cramer_orthogonal_of_descent nativePrimeTests hprime
      (nativePrimeTests_mono 4) nativePrimeTests_zero hdescent)

end PrimeUniformity

#print axioms OAI.Erdos3.exists_native_integer_interval_inverse
#print axioms PrimeUniformity.nativePrimeTests_inverse
#print axioms PrimeUniformity.nativePrimeTests_zero
#print axioms PrimeUniformity.nativePrimeTest_topInvariant_drop
#print axioms PrimeUniformity.nativePrimeTest_correlating_vertical_component_with_orbit
#print axioms PrimeUniformity.nativePrimeTest_correlating_vertical_component
#print axioms PrimeUniformity.nativePrimeTest_of_frozen_orbit
#print axioms PrimeUniformity.gowersUniformityEstimate_of_native_prime_descent
