import PrimeUniformity.TypeIIVaughanScale
import UpstreamTypeIICommonSamples
import UpstreamTypeIICommonRows
import UpstreamTypeIIProjectionBudget
import UpstreamTypeIIOrbitRecovery
import UpstreamTypeIIBranchFinish

namespace PrimeUniformity

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration RationalFilteredNilmanifold VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- Geometry and common-symbol coordinate bounds on the paired native model. -/
def typeIIVaughanGeometryBudget (s C : ℕ) (p : ℝ) : ℝ :=
  p + (p + 2) ^ 2 + ((111 * p + C) ^ C + s) +
    ((111 * p + C) ^ C + (s : ℝ) * (121 * p + 11 * p))

/-- Complexity sufficient for the exact three-factor output and the
bounded bases of the saturated single-axis layers. -/
noncomputable def typeIIVaughanFactorBudget (s C D : ℕ) (p : ℝ) : ℝ :=
  let z := typeIIVaughanGeometryBudget s C p
  let t := typeIIProjectionBudget s z
  let a := (D : ℝ) * t ^ 2
  p + preimageBasisBudget (typeIIPairedGeneratorBudget z + z + adaptedMarkedMapHeightBudget z) +
    (s : ℝ) * (a + 2) ^ 36 + ((a + 2) ^ 18 + a)

/-- The actual masked Vaughan Type II block recovers normalized
single-orbit factors at explicit polynomial logarithmic budgets. -/
theorem exists_typeII_native_factors_of_vaughan (s : ℕ) (hs : 1 ≤ s) :
    ∃ C D : ℕ, 2 ≤ C ∧ 1 ≤ D ∧
      ∀ {r X : ℕ} {p : ℝ} (Z : NativeRankedPrimeTest s (r + 1) X p)
        (ω : Fin Z.test.dim → ℕ),
      (∀ d, Z.test.model.filtration.layer d =
        Submodule.span ℚ (Z.test.model.basis '' {i | d ≤ ω i})) →
      Z.test.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Z.test.test.orbit = 1 →
      ∀ η : Z.test.L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (Z.test.model.basis i)) ≤ p) →
      (∀ x ∈ Z.test.model.filtration.realification.subgroup s, ∀ y,
        Z.test.test.observable (x • y) = CircleFourier.character
          ((realifyFunctional η x.coord : ℝ) : CircleFourier.Circle) * Z.test.test.observable y) →
      1 < X → max 2 (Real.log (Real.log (X : ℝ))) ≤ p → (Z.test.q : ℝ) ≤ Real.exp (11 * p) →
      (111 * p + C) ^ C + 132 * p + Real.log 2 ≤ Real.log (X : ℝ) / 4 →
      let t := typeIIProjectionBudget s (typeIIVaughanGeometryBudget s C p)
      (D : ℝ) * t + Real.log 4 ≤ Real.log (X : ℝ) / 4 →
      Real.exp (separationBudget ((D : ℝ) * t ^ 2)) ≤ X →
      let A := (Finset.Ioc Z.test.U Z.test.V).filter (fun n => n % Z.test.q = Z.test.a.val)
      let F : ℕ → ℂ := fun n => Z.test.test.eval (fun _ => (n : ℤ))
      ∀ i j : ℕ,
      (X : ℝ) * Real.exp (-20 * p) <
        ‖vaughanTypeIIBlock X X.sqrt.sqrt X.sqrt.sqrt i j A F‖ →
      NativeTypeIIOrbitFactors Z η (typeIIVaughanFactorBudget s C D p) := by
  obtain ⟨C, hC, hsample⟩ := exists_native_typeII_common_dilation_family s hs
  obtain ⟨Brec, hBrec, hrecover⟩ := exists_typeII_orbit_of_bounded_dilation_rows s hs
  refine ⟨C, Brec, hC, hBrec, ?_⟩
  intro r X p Z ω hω hzero η hη hvert hX hp hq hnative t hscale hsep A f i j hlarge
  let D := Z.test.model
  let R := Z.rank
  let T := Z.test.test
  let Pair := (pi (pairModels D D)).filtration
  let d := finrank ℚ (PairAlgebra Z.test.L Z.test.L)
  let B₀ := (111 * p + C) ^ C + s
  let P := (111 * p + C) ^ C + (s : ℝ) * (121 * p + 11 * p)
  let z := typeIIVaughanGeometryBudget s C p
  let Hrec := (Brec : ℝ) * t ^ 2
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀ : 0 ≤ p := by linarith
  have hX₀ : 0 < X := by omega
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := (T.norm_eval_le _).trans Z.test.bound
  have hA : A ⊆ Finset.Ioc 0 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt h.1, h.2.trans Z.test.endpoints.2.1⟩
  have hmass := large_prime_typeIIBlock_card_product hX A f (fun n _ => hf n)
    ((le_max_right _ _).trans hp) hlarge
  have hpositive : 0 < ((dyadicFactorBlock X.sqrt.sqrt X i).card : ℝ) *
      ((dyadicFactorBlock X.sqrt.sqrt X j).card : ℝ) :=
    (mul_pos (Nat.cast_pos.mpr hX₀) (Real.exp_pos _)).trans hmass
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (Nat.cast_pos.mp (pos_of_mul_pos_left hpositive (Nat.cast_nonneg _)))
  have hi : X.sqrt.sqrt < 2 ^ (i + 1) :=
    (mem_dyadicFactorBlock.mp hv).1.trans (mem_dyadicFactorBlock.mp hv).2.2.2
  have hinput := typeII_dilation_input_scale hX₀ hi Z.test.endpoints.2.2 hq hnative
  obtain ⟨b, w, hb, W, l, u, S, hS, _, hsize, hbH, hu, _, huH, hl, hlP, htop, hfac⟩ :=
    hsample D T η p Z.test.complexity Z.test.bound hη hvert hX Z.test.endpoints.2.1
      Z.test.endpoints.2.2 hp hq hinput hlarge
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hz₀ : 0 ≤ z := by
    change 0 ≤ p + (p + 2) ^ 2 + B₀ + P
    positivity
  have hpz : p ≤ z := by
    change p ≤ p + (p + 2) ^ 2 + B₀ + P
    linarith [sq_nonneg (p + 2)]
  have hBz : B₀ ≤ z := by
    change B₀ ≤ p + (p + 2) ^ 2 + B₀ + P
    linarith [sq_nonneg (p + 2)]
  have hPz : P ≤ z := by
    change P ≤ p + (p + 2) ^ 2 + B₀ + P
    linarith [sq_nonneg (p + 2)]
  have hpairsq : (p + 2) ^ 2 ≤ z := by
    change (p + 2) ^ 2 ≤ p + (p + 2) ^ 2 + B₀ + P
    linarith
  have hbool : (Fintype.card Bool : ℝ) ≤ p := by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp₂
  have hPair := (pi_geometry (pairModels D D) hp₀ hbool
    (fun c => by cases c <;> exact Z.complexity.1)).mono _ hpairsq
  have hdegree : (Fintype.card (Fin d) : ℝ) ≤ z := by
    have hd : d = Fintype.card (Σ c : Bool, Fin (Bool.rec Z.test.dim Z.test.dim c)) :=
      (finrank_eq_card_basis (pi (pairModels D D)).basis).trans (Fintype.card_fin _)
    rw [Fintype.card_fin, hd]
    exact hPair.1
  have hR : R.ComplexityLE z := Z.complexity.mono R hpz
  have hbz (a j) : rationalLogHeight ((pi (pairModels D D)).basis.repr (b a) j) ≤ z :=
    (hbH a j).trans hBz
  have huz (a j) : rationalLogHeight ((Pair.associatedGradedBasis b w hb).repr (u a) j) ≤ z :=
    (huH a j).trans hPz
  let Fst := Pair.gradedRefiltrationLayer W
  let U : Fin s → Submodule ℚ Z.test.L := fun d =>
    nativeTypeIIAxisSaturatedLayer R.filtration Fst (d.val + 1)
  have htopPair := Pair.frequency_zero_on_refiltered_top b w hb W (pairFrequency η (-η)) htop
  obtain ⟨hU, hTwo, htopU⟩ := nativeTypeII_saturated_geometry D R W η htopPair
  have hBases (j : Fin s) := exists_typeII_native_bounded_saturated_bases
    D R Pair b w hb W u hu hz₀ hR hPair hdegree hdegree hbz huz j
  choose e he using hBases
  obtain ⟨B, J, hB, hBexp, hJ, ξ, θ, m, hker, hξ, hθ, hm, hnear⟩ :=
    exists_typeII_common_native_rows D R hs T b w hb W u hu hz₀ hR hPair hdegree hdegree hbz huz
      P l hl S (by positivity : 0 < (2 : ℝ) ^ i) hfac
  have hdz : (d : ℝ) ≤ z := by simpa only [Fintype.card_fin] using hdegree
  obtain ⟨ht, hzt, h21, hcount, hbudget, hBheight, hmH, hH⟩ :=
    typeIIProjectionBudget_bounds (s := s) hz₀ hp₀ hpz hB₀ hBz hP hPz hdz hBexp hlP
  obtain ⟨_hLpos, _, hL, hside, hX₀lower, hY, _, hM⟩ :=
    typeII_vaughan_fourth_root_scales hX A hA f (fun n _ => hf n) hp h21 hscale hlarge
  let L := 2 ^ (j + 1) - 1
  let X₀ : ℕ := 2 ^ i * 2 ^ j
  let N : ℕ := d * (s + 1) * 2 ^ s
  let H : ℝ := (l : ℝ) * (N : ℝ) * (B ^ N : ℕ) * Real.exp P
  have hsidepos : 0 < (X₀ : ℝ) / L := (Real.exp_pos _).trans_le hside
  have hsmall (v : ℕ × ℕ) (hv : v ∈ S) (d : Fin s) (a : Fin (J d)) :
      ∃ b : ℤ, |((m d a : ℝ) * θ d a true) * (v.1 : ℝ) ^ (d.val + 1) +
        ((m d a : ℝ) * θ d a false) * (v.2 : ℝ) ^ (d.val + 1) - b| ≤
          H / ((X₀ : ℝ) / L) ^ (d.val + 1) := by
    obtain ⟨b, hh⟩ := hnear v hv d a
    refine ⟨b, ?_⟩
    have hh' : |((m d a : ℝ) * θ d a true) * (v.1 : ℝ) ^ (d.val + 1) +
        ((m d a : ℝ) * θ d a false) * (v.2 : ℝ) ^ (d.val + 1) - b| ≤
          H / ((2 : ℝ) ^ i) ^ (d.val + 1) := by
      simpa only [Fintype.card_fin] using hh
    exact hh'.trans (div_le_div_of_nonneg_left (by dsimp only [H]; positivity)
      (pow_pos hsidepos _) (pow_le_pow_left₀ hsidepos.le hY _))
  have hS' : S ⊆ dyadicDilationInterval L ×ˢ dyadicDilationInterval L := by
    intro v hv
    have hm := Finset.mem_product.mp (hS hv)
    exact Finset.mem_product.mpr ⟨hM hm.1, hM hm.2⟩
  have hdense : Real.exp (-t) * ((dyadicDilationInterval L).card : ℝ) ^ 2 ≤ S.card := by
    rw [card_dyadicDilationInterval_pow_sub_one, Nat.cast_pow, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget))
      (sq_nonneg _)).trans hsize
  have hcard : (Fintype.card ((Σ a : Fin s, Fin (J a)) × Bool) : ℝ) ≤ t := by
    have hsum : (∑ a : Fin s, J a) ≤ s * d := by
      calc
        _ ≤ ∑ _ : Fin s, d := Finset.sum_le_sum (fun a _ => by
          simpa only [Fintype.card_fin] using hJ a)
        _ = _ := by simp
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    have hsum' : ((∑ a : Fin s, J a : ℕ) : ℝ) ≤ (s : ℝ) * d := by exact_mod_cast hsum
    nlinarith only [hcount, hsum']
  have hhn : (Z.test.dim : ℝ) ≤ t := Z.test.complexity.1.1.trans (hpz.trans hzt)
  have hhJ (j : Fin s) : (Fintype.card (Fin (J j)) : ℝ) ≤ t := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr (hJ j)).trans (hdegree.trans hzt)
  obtain ⟨q, hqpos, hqB, ε, g, ρ, _, hg0, _, hε, hρ, hprod, hg⟩ :=
    hrecover D R ω hω U (fun d => hU (d.val + 1)) (fun d => hTwo (d.val + 1))
      ξ hker T.orbit hzero θ hθ (one_le_ceil_exp _) hξ ht hhn hhJ hBheight
      (by dsimp only [H]; positivity : 0 ≤ H) hH hcard hL hside (Nat.cast_pos.mpr hX₀) hX₀lower hsep
      S hS' hdense m (fun d j => (hm d j).1)
      (fun d j => (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using (hm d j).2)).trans hmH) hsmall
  let Ψ := preimageBasisBudget (typeIIPairedGeneratorBudget z + z + adaptedMarkedMapHeightBudget z)
  let Q := (s : ℝ) * (Hrec + 2) ^ 36
  let E := (Hrec + 2) ^ 18 + Hrec
  let a := typeIIVaughanFactorBudget s C Brec p
  have hΨ₀ : 0 ≤ Ψ := by
    apply preimageBasisBudget_nonneg
    have h₁ : 0 ≤ refiltrationCoordinateBudget z := refiltrationCoordinateBudget_nonneg hz₀
    dsimp only [typeIIPairedGeneratorBudget, adaptedMarkedMapHeightBudget]
    positivity
  have hQ₀ : 0 ≤ Q := by dsimp only [Q, Hrec]; positivity
  have hE₀ : 0 ≤ E := by dsimp only [E, Hrec]; positivity
  have ha : a = p + Ψ + Q + E := rfl
  have ha₀ : 0 ≤ a := by rw [ha]; positivity
  have hE : E ≤ (a + 2) ^ 19 := by
    have hEa : E ≤ a := by rw [ha]; linarith
    exact hEa.trans ((show a ≤ a + 2 by linarith).trans (le_self_pow₀ (by linarith) (by decide)))
  have hΨ : Ψ ≤ a := by rw [ha]; linarith
  have hQa : Q ≤ a := by rw [ha]; linarith
  refine ⟨U, e, fun d => hU (d.val + 1), fun d j k => (he d j k).trans hΨ,
    ?_, q, hqpos, hqB.trans (Real.exp_le_exp.mpr hQa), ε, g, ρ, hg0,
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr hX₀) hε (Real.exp_le_exp.mpr hE),
    hρ, hprod, hg⟩
  intro a hd hr
  exact htopU (SubspaceFreeLift.weight U) a hd hr (fun i => (e i.1 i.2 : Z.test.L))
    (fun i => (e i.1 i.2).property)

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeII_native_factors_of_vaughan
