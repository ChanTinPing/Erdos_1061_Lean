import OAI.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
import OAI.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
import OAI.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
import OAI.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
import OAI.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

section

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

/-- At each degree the possible generators are the fast space together with
the residual rank-two space. -/
noncomputable abbrev fastRankLayer (j : ℕ) : Submodule ℚ L :=
  D.filtration.gradedRefiltrationLayer W j ⊔ R.filtration.layer j 2

variable {D R W} in
theorem fastRankLayer_le (j : ℕ) : fastRankLayer D R W j ≤ D.filtration.layer j := by
  refine sup_le (D.filtration.gradedRefiltrationLayer_le W j) ?_
  rw [← R.associated]
  exact R.filtration.layer_le_associatedDegree j 2

/-- At the current top degree and rank, only the fast parts of the
generators contribute to the bracket evaluated by the frequency. -/
theorem fastRank_lieTree_frequency_zero (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ D.filtration.gradedRefiltrationLayer W s,
      x ∈ R.filtration.layer s r → η x = 0)
    {X : Type*} (w : X → ℕ) (v : X → L)
    (hv : ∀ i, v i ∈ fastRankLayer D R W (w i))
    (a : FreeMagma X) (ha : lieTreeWeight w a = s) (hr : a.length = r) :
    η (lieTreeEval v a) = 0 := by
  classical
  choose u hu k hk heq using fun i => Submodule.mem_sup.mp (hv i)
  have hsub (i : X) : v i - u i ∈ R.filtration.layer (w i) 2 := by
    rw [← heq i]
    simpa only [add_sub_cancel_left] using hk i
  have hRankOne {z : L} {j : ℕ} (hz : z ∈ D.filtration.layer j) :
      z ∈ R.filtration.layer j 1 := by
    rwa [← R.associated, DegreeRankLieFiltration.associatedDegree_layer,
      R.filtration.rank_zero_eq_one] at hz
  have hv₁ (i : X) : v i ∈ R.filtration.layer (w i) 1 :=
    hRankOne (fastRankLayer_le (w i) (hv i))
  have hu₁ (i : X) : u i ∈ R.filtration.layer (w i) 1 :=
    hRankOne (D.filtration.gradedRefiltrationLayer_le W (w i) (hu i))
  rw [R.filtration.top_lieTreeEval_congr v u w hv₁ hu₁ hsub a ha hr]
  exact hη _ (by simpa only [ha] using D.filtration.refiltered_lieTreeEval_mem W w u hu a)
    (by simpa only [ha, hr] using R.filtration.lieTreeEval_mem_length u w hu₁ a)

/-- Bounded bases of the fast layers extend to bounded bases of the
coefficient spaces by adjoining the degree-rank basis in rank two. -/
theorem exists_fastRankLayer_basis (hs : 2 ≤ s) {p : ℝ} (hR : R.ComplexityLE p)
    (j : Fin s)
    (a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W (j.val + 1)))) ℚ
      (D.filtration.gradedRefiltrationLayer W (j.val + 1)))
    (ha : ∀ i k, rationalLogHeight (D.basis.repr (a i : L) k) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (fastRankLayer D R W (j.val + 1)))) ℚ
        (fastRankLayer D R W (j.val + 1)),
      ∀ i k, rationalLogHeight (D.basis.repr (b i : L) k) ≤ p := by
  let j₀ : Fin (s + 1) := ⟨j.val + 1, by omega⟩
  let two : Fin (s + 1) := ⟨2, by omega⟩
  let b := R.basis j₀ two
  let v := Sum.elim (fun i => (a i : L)) (fun i => (b i : L))
  have hspan : Submodule.span ℚ (Set.range v) = fastRankLayer D R W (j.val + 1) := by
    dsimp only [v]
    rw [span_range_sumElim]
    change _ = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔
      R.filtration.layer (j.val + 1) 2
    congr 1 <;> apply (Submodule.span_range_subtype_eq_top_iff _ _).mp <;> exact Basis.span_eq _
  exact exists_submodule_basis_of_spanning_logHeight D.basis _ v hspan (fun i => by
    cases i with
    | inl i => exact ha i
    | inr i => exact hR.2 j₀ two i)

/-- A rank-two residual and a fast orbit multiply to a polynomial orbit
whose actual coefficients meet the requirements of the free rank lift. -/
theorem fastRank_product_coefficients (hs : 1 ≤ s)
    (K U : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hK : ∀ j : Fin s, coefficients K.log (Finsupp.single () (j.val + 1)) ∈
      (R.filtration.layer (j.val + 1) 2).baseChange ℝ)
    (hU : ∀ j : Fin s, coefficients U.log (Finsupp.single () (j.val + 1)) ∈
      D.filtration.realGradedRefiltrationLayer W (j.val + 1)) :
    ∀ j : Fin s, coefficients (K * U).log (Finsupp.single () (j.val + 1)) ∈
      (fastRankLayer D R W (j.val + 1)).baseChange ℝ := by
  intro j
  let α : Unit →₀ ℕ := Finsupp.single () (j.val + 1)
  have hBCH := R.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs (fun _ : Unit => 1) α K U
  simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one] at hBCH
  have hRle : (R.filtration.layer (j.val + 1) 2).baseChange ℝ ≤
      (fastRankLayer D R W (j.val + 1)).baseChange ℝ := Submodule.baseChange_mono ℝ le_sup_right
  have hUle : D.filtration.realGradedRefiltrationLayer W (j.val + 1) ≤
      (fastRankLayer D R W (j.val + 1)).baseChange ℝ := Submodule.baseChange_mono ℝ le_sup_left
  have hsum := Submodule.add_mem ((fastRankLayer D R W (j.val + 1)).baseChange ℝ)
    (hRle hBCH) (Submodule.add_mem _ (hRle (hK j)) (hUle (hU j)))
  simpa only [sub_add_cancel] using hsum

end

/-- Lift a normalized orbit to a bounded free degree-rank model when the
vertical frequency vanishes on the leading brackets of its generators. -/
theorem exists_native_rank_lift (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ L) (b : ∀ i, Basis (Fin (finrank ℚ (S i))) ℚ (S i))
      (_hS : ∀ i : Fin s, S i ≤ R.filtration.layer (i.val + 1) 0)
      (η : L →ₗ[ℚ] ℚ)
      (_hη : ∀ a : FreeMagma (SubspaceFreeLift.Alphabet S),
        lieTreeWeight (SubspaceFreeLift.weight S) a = s → a.length = r →
          η (lieTreeEval (fun i => (b i.1 i.2 : L)) a) = 0)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (_hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
      {p : ℝ},
      0 ≤ p → R.ComplexityLE p →
        (∀ j a i, rationalLogHeight (D.basis.repr (b j a : L) i) ≤ p) →
        (∀ i : Fin s, coefficients g.log (Finsupp.single () (i.val + 1)) ∈ (S i).baseChange ℝ) →
        ∃ E : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
            (finrank ℚ (SubspaceFreeLift.Algebra S r)),
          ∃ Q : E.DegreeRankStructure r,
            Q.ComplexityLE ((p + C) ^ C) ∧
            ∃ φ : SubspaceFreeLift.Algebra S r →ₗ⁅ℚ⁆ L,
              (∀ j k x, x ∈ Q.filtration.layer j k → φ x ∈ R.filtration.layer j k) ∧
              (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
              E.lattice ≤ D.lattice.comap (mapOfSteps
                (hL := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ) ∧
              ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                let Φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                  (hM := D.filtration.lowerCentralSeries_eq_bot) φ
                E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
                (∀ x : Unit → ℤ, Φ (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x u) =
                  D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g) ∧
                ∀ z ∈ Q.realSubgroup s r,
                  Φ z ∈ R.realSubgroup s r ∧ Φ z ∈ D.filtration.realification.subgroup s ∧
                    realifyFunctional η (Φ z).coord = 0 := by
  obtain ⟨A, _, hfree⟩ := exists_native_free_evaluation s
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C (s + 1) * X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d r D R S b hS η hη g hg p hp hR hb hgcoeff
  classical
  let : Module.Finite ℚ L := D.basis.finiteDimensional_of_finite
  let Y := SubspaceFreeLift.Alphabet S
  let w := SubspaceFreeLift.weight S
  let hw := SubspaceFreeLift.weight_pos S
  let q := ((s + 1 : ℕ) : ℝ) * p + 1
  have hpq : p ≤ q := by
    dsimp only [q]
    push_cast
    nlinarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg s]
  have hq : 0 ≤ q := hp.trans hpq
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hR.1.1
  have hcard : (Fintype.card Y : ℝ) ≤ q := by
    calc
      _ ≤ (s : ℝ) * finrank ℚ L := by exact_mod_cast SubspaceFreeLift.alphabet_card_le S
      _ ≤ (s : ℝ) * p := mul_le_mul_of_nonneg_left hdim (Nat.cast_nonneg _)
      _ ≤ q := by dsimp only [q]; push_cast; nlinarith
  have hcost : (q + A) ^ A ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  let f (i : Y) := (b i.1 i.2 : L)
  have hf (i : Y) : f i ∈ R.filtration.layer (w i) 0 := hS i.1 (b i.1 i.2).property
  obtain ⟨E, Q, hQ, hQc, _, _, hheight, hlattice⟩ :=
    hfree Y L r d R.filtration.rank_le_degree D R w hw f hf q hq hcard
      (hR.mono R hpq) (fun a i => (hb a.1 a.2 i).trans hpq)
  let φ := SubspaceFreeLift.evaluation S b R.filtration hS
  have hφ j k x (hx : x ∈ Q.filtration.layer j k) : φ x ∈ R.filtration.layer j k := by
    rw [hQ] at hx
    exact FreeDegreeRankLieAlgebra.lift_mem_layer R.filtration w hw f hf
      R.filtration.rank_le_degree hx
  obtain ⟨u, hu, _, _, hueval⟩ := SubspaceFreeLift.exists_native_polynomialOrbit
    D R S b hS E Q hQ g hg hgcoeff
  refine ⟨E, Q, hQc.mono Q hcost, φ, hφ, (fun i j => (hheight i j).trans hcost),
    hlattice, u, hu, hueval, ?_⟩
  intro z hz
  have hker : Q.filtration.layer s r ≤ LinearMap.ker (η.comp φ.toLinearMap) := by
    intro x hx
    rw [hQ] at hx
    exact FreeDegreeRankLieAlgebra.lift_top_frequency_zero R.filtration w hw f hf η hη hx
  have hz' : z.coord ∈ (Q.filtration.layer s r).baseChange ℝ := hz
  have hzmap := baseChange_mem_of_mapsTo (Q.filtration.layer s r) (R.filtration.layer s r)
    φ.toLinearMap (hφ s r) hz'
  refine ⟨hzmap, ?_, ?_⟩
  · have hle : R.filtration.layer s r ≤ D.filtration.layer s := by
      rw [← R.associated]
      exact R.filtration.layer_le_associatedDegree s r
    exact Submodule.baseChange_mono ℝ hle hzmap
  · have hzker := (mem_realified_frequency_kernel_iff (η.comp φ.toLinearMap) z.coord).mp
      (Submodule.baseChange_mono ℝ hker hz')
    rw [realifyFunctional_comp] at hzker
    exact hzker

/-- A fast component together with a rank-two residual satisfies the
leading-bracket hypothesis if the frequency kills its fast top rank. -/
theorem exists_native_fast_rank_lift (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (η : L →ₗ[ℚ] ℚ)
      (_hη : ∀ x ∈ D.filtration.gradedRefiltrationLayer W s,
        x ∈ R.filtration.layer s r → η x = 0)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (_hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
      {p : ℝ},
      0 ≤ p → R.ComplexityLE p →
      let S (i : Fin s) := fastRankLayer D R W (i.val + 1)
      ∀ (b : ∀ i, Basis (Fin (finrank ℚ (S i))) ℚ (S i)),
        (∀ j a i, rationalLogHeight (D.basis.repr (b j a : L) i) ≤ p) →
        (∀ i : Fin s, coefficients g.log (Finsupp.single () (i.val + 1)) ∈ (S i).baseChange ℝ) →
        ∃ E : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
            (finrank ℚ (SubspaceFreeLift.Algebra S r)),
          ∃ Q : E.DegreeRankStructure r,
            Q.ComplexityLE ((p + C) ^ C) ∧
            ∃ φ : SubspaceFreeLift.Algebra S r →ₗ⁅ℚ⁆ L,
              (∀ j k x, x ∈ Q.filtration.layer j k → φ x ∈ R.filtration.layer j k) ∧
              (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
              E.lattice ≤ D.lattice.comap (mapOfSteps
                (hL := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ) ∧
              ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                let Φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                  (hM := D.filtration.lowerCentralSeries_eq_bot) φ
                E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
                (∀ x : Unit → ℤ, Φ (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
                  D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g) ∧
                ∀ z ∈ Q.realSubgroup s r,
                  Φ z ∈ R.realSubgroup s r ∧ Φ z ∈ D.filtration.realification.subgroup s ∧
                    realifyFunctional η (Φ z).coord = 0 := by
  obtain ⟨C, hC, hlift⟩ := exists_native_rank_lift s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d r D R W η hη g hg p hp hR S b hb hgcoeff
  have hS (i : Fin s) : S i ≤ R.filtration.layer (i.val + 1) 0 := by
    change S i ≤ R.filtration.associatedDegree.layer (i.val + 1)
    rw [R.associated]
    exact fastRankLayer_le (i.val + 1)
  exact hlift D R S b hS η
    (fastRank_lieTree_frequency_zero D R W η hη (SubspaceFreeLift.weight S)
      (fun i => (b i.1 i.2 : L)) (fun i => (b i.1 i.2).property)) g hg hp hR hb hgcoeff

end PrimeUniformity
