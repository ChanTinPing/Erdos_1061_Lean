import PrimeUniformity.TypeIIDilationBudget
import PrimeUniformity.UpstreamTypeICoefficientLift
import PrimeUniformity.UpstreamTypeIRankReassembly
import UpstreamTypeIIAxisSaturation

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration RationalFilteredNilmanifold
open Module VectorPolynomial
open scoped BigOperators TensorProduct

section SaturatedGeometry

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)

local notation "F₂" => (RationalFilteredNilmanifold.filtration (pi (pairModels D D)))

/-- The saturated first-axis layers of the common paired fast algebra have
the degree bounds and top-rank cancellation needed by native rank descent. -/
theorem nativeTypeII_saturated_geometry
    (W : LieSubalgebra ℚ (F₂).AssociatedGraded) (η : L →ₗ[ℚ] ℚ)
    (hTop : ∀ z ∈ (F₂).gradedRefiltrationLayer W s, pairFrequency η (-η) z = 0) :
    let A := (F₂).gradedRefiltrationLayer W
    let U := nativeTypeIIAxisSaturatedLayer R.filtration A
    (∀ d, U d ≤ D.filtration.layer d) ∧
    (∀ d, R.filtration.layer d 2 ≤ U d) ∧
    ∀ {I : Type*} (weight : I → ℕ) (a : FreeMagma I),
      lieTreeWeight weight a = s → a.length = r →
      ∀ x : I → L, (∀ i, x i ∈ U (weight i)) → η (lieTreeEval x a) = 0 := by
  intro A U
  have hLayer (d : ℕ) : D.filtration.layer d = R.filtration.layer d 1 := by
    rw [← R.filtration.rank_zero_eq_one]
    change D.filtration.layer d = R.filtration.associatedDegree.layer d
    rw [R.associated]
  have hA (d : ℕ) (z : PairAlgebra L L) (hz : z ∈ A d) :
      nativeTypeIIFirstProjection z ∈ R.filtration.layer d 1 ∧
      nativeTypeIISecondProjection z ∈ R.filtration.layer d 1 := by
    have hz' := (F₂).gradedRefiltrationLayer_le W d hz
    change z ∈ (NilpotentLieFiltration.pi (fun i => (pairModels D D i).filtration)).layer d at hz'
    rw [NilpotentLieFiltration.mem_pi_layer] at hz'
    rw [← hLayer]
    exact ⟨hz' true, hz' false⟩
  have hU (d : ℕ) : U d ≤ D.filtration.layer d := by
    rw [hLayer]
    exact nativeTypeIIAxisSaturatedLayer_le_rank_one R.filtration A (fun d z hz => (hA d z hz).1) d
  refine ⟨hU, nativeTypeIIAxisSaturatedLayer_rank_two_le R.filtration A, ?_⟩
  intro I weight a hd hr x hx
  exact nativeTypeIIAxisSaturatedLayer_top_bracket_frequency R.filtration A weight a hd hr hA
    (fun _ _ _ _ hx hy => (F₂).gradedRefiltrationLayer_lie_mem W hx hy) η hTop x hx

end SaturatedGeometry

/-- Recover a normalized native factorization from the undilated axis row
estimates. The middle orbit stays in the supplied saturated degree layers. -/
theorem exists_typeII_orbit_of_saturated_rows
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
    {J : Fin s → Type*} [∀ d, Fintype (J d)]
    (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (ω : Fin n → ℕ) (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (A : Fin s → Submodule ℚ L)
    (hA : ∀ d, A d ≤ D.filtration.layer (d.val + 1))
    (hRankTwo : ∀ d, R.filtration.layer (d.val + 1) 2 ≤ A d)
    (η : ∀ d, L →ₗ[ℚ] (J d → ℚ)) (hker : ∀ d, LinearMap.ker (η d) = A d)
    {B l : ℕ} (hB : 1 ≤ B) (hl : 0 < l)
    (hheight : ∀ d i j, RationalHeightLE (η d (D.basis i) j) B)
    {p X : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p)
    (hJ : ∀ d, (Fintype.card (J d) : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (hX : Real.exp (separationBudget p) ≤ X)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (a : ∀ d, J d → ℤ)
    (hnear : ∀ d j, |(l : ℝ) * realifyCoordinateMap (η d)
      (coefficients g.log (Finsupp.single () (d.val + 1))) j - (a d j : ℝ)| ≤
        Real.exp p / X ^ (d.val + 1)) :
    let w : Unit → ℕ := fun _ => 1
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) ∧
      ∃ ε U ρ : D.filtration.realification.PolynomialOrbit w,
        D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
        D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
        D.filtration.realification.polynomialOrbitEval w 0 ρ = 1 ∧
        CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => X) (Real.exp ((p + 2) ^ 18 + p)) ε.log ∧
        CoefficientGrid (D.basis.baseChange ℝ) m ρ.log ∧ ε * U * ρ = g ∧
        ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈ (A d).baseChange ℝ := by
  intro w
  have hx (d : Fin s) : coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.filtration.layer (d.val + 1)).baseChange ℝ := by
    change coefficients g.log (Finsupp.single () (d.val + 1)) ∈ D.filtration.realification.layer (d.val + 1)
    have h := (D.filtration.realification.adapted_iff_coefficients _ _).mp g.adapted
      (Finsupp.single () (d.val + 1))
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
  have hι : (Fintype.card (Fin n) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hn
  have hlift (d : Fin s) := exists_typeI_layer_coefficient_lifts
    D.basis (D.filtration.layer (d.val + 1)) (A d) {i | d.val + 1 ≤ ω i} (hF _)
    (η d) (hker d) hB hl (Nat.succ_pos d.val) (hheight d) hp hι (hJ d) hBp hlp hX
    (coefficients g.log (Finsupp.single () (d.val + 1))) (hx d) (a d) (hnear d)
  choose m hm hmp e q he hq heBound hqGrid hres using hlift
  have hres' (d : Fin s) : coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d) ∈
      (A d ⊔ R.filtration.layer (d.val + 1) 2).baseChange ℝ := by
    rw [sup_eq_left.mpr (hRankTwo d)]
    exact hres d
  obtain ⟨hmprod, _, ε, K, U, ρ, _, _, hε0, hK0, hU0, hρ0, hslow, hgrid, hprod, hlayer⟩ :=
    exists_rank_two_reassembly_of_layers D R hs g hg A hA e q he hq
      ((Real.exp_pos _).trans_le hX) (Real.exp_pos _).le heBound m hm hqGrid hres'
  have hmBound : ((∏ d, m d : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) := by
    rw [Nat.cast_prod, Real.exp_nat_mul]
    calc
      _ ≤ ∏ _ : Fin s, Real.exp ((p + 2) ^ 36) := by gcongr with d; exact hmp d
      _ = _ := by simp
  refine ⟨∏ d, m d, hmprod, hmBound, ε, K * U, ρ, hε0, ?_, hρ0, hslow, hgrid, ?_, ?_⟩
  · rw [map_mul, hK0, hU0, mul_one]
  · simpa only [mul_assoc] using hprod
  · intro d
    let α : Unit →₀ ℕ := Finsupp.single () (d.val + 1)
    have hBCH := R.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs (fun _ : Unit => 1) α K U
    simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one] at hBCH
    have hle := Submodule.baseChange_mono ℝ (hRankTwo d)
    have hsum := Submodule.add_mem ((A d).baseChange ℝ) (hle hBCH)
      (Submodule.add_mem _ (hle (hlayer d).1) (hlayer d).2)
    simpa only [sub_add_cancel] using hsum

/-- Dense paired row estimates recover the undilated first-axis coefficients
and hence a normalized factorization of the native orbit. -/
theorem exists_typeII_orbit_of_bounded_dilation_rows (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {n r : ℕ}
        {J : Fin s → Type*} [∀ d, Fintype (J d)]
        (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)
        (ω : Fin n → ℕ) (_hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (D.basis '' {i | k ≤ ω i}))
        (A : Fin s → Submodule ℚ L) (_hA : ∀ d, A d ≤ D.filtration.layer (d.val + 1))
        (_hRankTwo : ∀ d, R.filtration.layer (d.val + 1) 2 ≤ A d)
        (η : ∀ d, L →ₗ[ℚ] (J d → ℚ)) (_hker : ∀ d, LinearMap.ker (η d) = A d)
        (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (_hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
        (θ : ∀ j, J j → Bool → ℝ),
      (∀ d j, θ d j true = realifyCoordinateMap (η d)
        (coefficients g.log (Finsupp.single () (d.val + 1))) j) →
      ∀ {B l : ℕ}, 1 ≤ B →
      (∀ d i j, RationalHeightLE (η d (D.basis i) j) B) →
      ∀ {t H X₀ X : ℝ}, 1 ≤ t → (n : ℝ) ≤ t → (∀ d, (Fintype.card (J d) : ℝ) ≤ t) →
      (B : ℝ) ≤ Real.exp t → 0 ≤ H → H ≤ Real.exp t →
      (Fintype.card ((Σ j : Fin s, J j) × Bool) : ℝ) ≤ t →
      Real.exp ((C : ℝ) * t) ≤ l → Real.exp ((C : ℝ) * t) ≤ X₀ / l →
      0 < X → X * Real.exp (-t) ≤ X₀ →
      Real.exp (separationBudget ((C : ℝ) * t ^ 2)) ≤ X →
      ∀ (S : Finset (ℕ × ℕ)), S ⊆ dyadicDilationInterval l ×ˢ dyadicDilationInterval l →
      Real.exp (-t) * ((dyadicDilationInterval l).card : ℝ) ^ 2 ≤ S.card →
      ∀ (m : ∀ j, J j → ℕ), (∀ j i, 0 < m j i) → (∀ j i, (m j i : ℝ) ≤ Real.exp t) →
      (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * θ j i true) * (d.1 : ℝ) ^ (j.val + 1) +
          ((m j i : ℝ) * θ j i false) * (d.2 : ℝ) ^ (j.val + 1) - a| ≤
            H / (X₀ / l) ^ (j.val + 1)) →
      let p := (C : ℝ) * t ^ 2
      let w : Unit → ℕ := fun _ => 1
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) ∧
        ∃ ε U ρ : D.filtration.realification.PolynomialOrbit w,
          D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
          D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
          D.filtration.realification.polynomialOrbitEval w 0 ρ = 1 ∧
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => X) (Real.exp ((p + 2) ^ 18 + p)) ε.log ∧
          CoefficientGrid (D.basis.baseChange ℝ) q ρ.log ∧ ε * U * ρ = g ∧
          ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈ (A d).baseChange ℝ := by
  obtain ⟨C, hC, hrec⟩ := exists_uniform_typeII_coefficient_recovery s
  refine ⟨C, hC, ?_⟩
  intro L _ _ n r J _ D R ω hF A hA hRankTwo η hker g hg θ hθ
    B l hB hheight t H X₀ X ht hn hJ hBt hH hHt hcard hl hside hX hX₀ hsep S hS hdense
    m hm hmt hnear p w
  have htp : t ≤ p := by
    have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp only [p]
    calc
      t ≤ t ^ 2 := le_self_pow₀ ht (by decide)
      _ = 1 * t ^ 2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hC' (sq_nonneg t)
  have hp : 0 ≤ p := (zero_le_one.trans ht).trans htp
  obtain ⟨q, hq, hqp, happ⟩ :=
    hrec θ m hm l ht hH hHt hmt hcard hl hside hX hX₀ S hS hdense hnear
  have hnear' (d : Fin s) (j : J d) : ∃ a : ℤ, |(q : ℝ) * realifyCoordinateMap (η d)
      (coefficients g.log (Finsupp.single () (d.val + 1))) j - (a : ℝ)| ≤
        Real.exp p / X ^ (d.val + 1) := by
    simpa only [hθ] using happ d j true
  choose a ha using hnear'
  exact exists_typeII_orbit_of_saturated_rows D R hs ω hF A hA hRankTwo η hker
    hB hq hheight hp (hn.trans htp) (fun d => (hJ d).trans htp)
    (hBt.trans (Real.exp_le_exp.mpr htp)) hqp hsep g hg a ha

end PrimeUniformity

#print axioms PrimeUniformity.nativeTypeII_saturated_geometry
#print axioms PrimeUniformity.exists_typeII_orbit_of_saturated_rows
#print axioms PrimeUniformity.exists_typeII_orbit_of_bounded_dilation_rows
