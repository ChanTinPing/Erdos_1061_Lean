import UpstreamFastOrbitRealization
import OAI.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
import OAI.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization
import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

section

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure 1)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

/-- Add the rank-two residual space to each fast refiltered layer. -/
noncomputable def rankOneFastLayer (j : ℕ) : Submodule ℚ L :=
  D.filtration.gradedRefiltrationLayer W j ⊔ R.filtration.layer j 2

theorem rankOneFastLayer_le (j : ℕ) : rankOneFastLayer D R W j ≤ D.filtration.layer j := by
  refine sup_le (D.filtration.gradedRefiltrationLayer_le W j) ?_
  rw [← R.associated]
  exact R.filtration.layer_le_associatedDegree j 2

theorem rankOneFastLayer_antitone : Antitone (rankOneFastLayer D R W) := by
  intro i j hij
  exact sup_le_sup (D.filtration.gradedRefiltrationLayer_antitone W hij)
    (R.filtration.degree_antitone 2 hij)

private theorem mem_rankOne_layer_one {j : ℕ} {x : L}
    (hx : x ∈ D.filtration.gradedRefiltrationLayer W j) : x ∈ R.filtration.layer j 1 := by
  have hx' : x ∈ D.filtration.layer j := D.filtration.gradedRefiltrationLayer_le W j hx
  rwa [← R.associated, DegreeRankLieFiltration.associatedDegree_layer,
    R.filtration.rank_zero_eq_one] at hx'

theorem rankOneFastLayer_lie_mem {i j : ℕ} {x y : L}
    (hx : x ∈ rankOneFastLayer D R W i) (hy : y ∈ rankOneFastLayer D R W j) :
    ⁅x, y⁆ ∈ rankOneFastLayer D R W (i + j) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, e, he, rfl⟩ := Submodule.mem_sup.mp hy
  have hac := D.filtration.gradedRefiltrationLayer_lie_mem W ha hc
  have hae := R.filtration.rank_antitone (i + j) (by decide : 2 ≤ 1 + 2)
    (R.filtration.lie_mem (mem_rankOne_layer_one D R W ha) he)
  have hbc := R.filtration.rank_antitone (i + j) (by decide : 2 ≤ 2 + 1)
    (R.filtration.lie_mem hb (mem_rankOne_layer_one D R W hc))
  have hbe := R.filtration.rank_antitone (i + j) (by decide : 2 ≤ 2 + 2)
    (R.filtration.lie_mem hb he)
  rw [add_lie, lie_add, lie_add]
  exact (rankOneFastLayer D R W (i + j)).add_mem
    ((rankOneFastLayer D R W (i + j)).add_mem (Submodule.mem_sup_left hac) (Submodule.mem_sup_right hae))
    ((rankOneFastLayer D R W (i + j)).add_mem (Submodule.mem_sup_right hbc) (Submodule.mem_sup_right hbe))

theorem rankOneFastLayer_one :
    rankOneFastLayer D R W 1 = D.filtration.gradedRefiltrationLayer W 1 := by
  apply sup_eq_left.mpr
  rw [R.filtration.overshoot 1 2 (by decide)]
  have h : R.filtration.layer (1 + 1) 0 = D.filtration.layer (1 + 1) :=
    congrArg (fun F : NilpotentLieFiltration L s => F.layer (1 + 1)) R.associated
  rw [h]
  exact D.filtration.layer_succ_le_gradedRefiltrationLayer W 1

theorem rankOneFastLayer_top :
    rankOneFastLayer D R W s = D.filtration.gradedRefiltrationLayer W s := by
  rw [rankOneFastLayer, R.filtration.terminal, sup_bot_eq]

/-- The enlargement keeps the original fast rational Lie subalgebra and
changes only its filtration. -/
noncomputable def rankOneFastFiltration :
    NilpotentLieFiltration (D.filtration.gradedRefiltrationSubalgebra W) s where
  layer j := (rankOneFastLayer D R W j).comap (D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap
  antitone := fun _ _ hij _ hx => rankOneFastLayer_antitone D R W hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    change (x : L) ∈ rankOneFastLayer D R W 1
    rw [rankOneFastLayer_one]
    exact x.property
  lie_mem := fun hx hy => rankOneFastLayer_lie_mem D R W hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change (x : L) = 0
    have h : (x : L) ∈ D.filtration.layer (s + 1) := rankOneFastLayer_le D R W (s + 1) hx
    simpa only [D.filtration.terminal, Submodule.mem_bot] using h

theorem exists_rankOneFastLayer_basis (hs : 2 ≤ s) {p : ℝ} (hR : R.ComplexityLE p)
    (j : ℕ) (hj : j ≤ s)
    (a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
      (D.filtration.gradedRefiltrationLayer W j))
    (ha : ∀ i k, rationalLogHeight (D.basis.repr (a i : L) k) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (rankOneFastLayer D R W j))) ℚ (rankOneFastLayer D R W j),
      ∀ i k, rationalLogHeight (D.basis.repr (b i : L) k) ≤ p := by
  let j₀ : Fin (s + 1) := ⟨j, by omega⟩
  let two : Fin (s + 1) := ⟨2, by omega⟩
  let b := R.basis j₀ two
  let v := Sum.elim (fun i => (a i : L)) (fun i => (b i : L))
  have hspan : Submodule.span ℚ (Set.range v) = rankOneFastLayer D R W j := by
    dsimp only [v]
    rw [span_range_sumElim, rankOneFastLayer]
    congr 1 <;> apply (Submodule.span_range_subtype_eq_top_iff _ _).mp <;> exact Basis.span_eq _
  exact exists_submodule_basis_of_spanning_logHeight D.basis _ v hspan (fun i => by
    cases i with
    | inl i => exact ha i
    | inr i => exact hR.2 j₀ two i)

/-- Use the lattice and ambient basis of a controlled fast model, replacing
its filtered layer bases by bounded bases of the enlarged layers. -/
theorem exists_native_rankOneFast_model (hs : 2 ≤ s) {p : ℝ} (hp : 0 ≤ p)
    (hR : R.ComplexityLE p)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
      (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)))
    (hE : E.GeometryComplexityLE p)
    (hinc : ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ p)
    (hfast : ∀ j, 1 ≤ j → j ≤ s →
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
          (D.filtration.gradedRefiltrationLayer W j),
        ∀ i k, rationalLogHeight (D.basis.repr (b i : L) k) ≤ p) :
    ∃ E' : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
        (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
      E'.filtration = rankOneFastFiltration D R W ∧ E'.basis = E.basis ∧ E'.lattice = E.lattice ∧
      E'.GeometryComplexityLE (p + (p + 3) ^ 8) := by
  classical
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let F := rankOneFastFiltration D R W
  let A := ⌈Real.exp p⌉₊
  have hA : 1 ≤ A := one_le_ceil_exp p
  have hAp : (A : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp₁ : 0 ≤ p + 1 := by linarith
  have hpq : p ≤ p + (p + 3) ^ 8 := le_add_of_nonneg_right (by positivity)
  have hqp : (p + 3) ^ 8 ≤ p + (p + 3) ^ 8 := le_add_of_nonneg_left hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    rw [Fintype.card_fin]
    exact hR.1.1.trans (by linarith)
  have hH : (Fintype.card (Fin (finrank ℚ H)) : ℝ) ≤ p + 1 := by
    rw [Fintype.card_fin]
    exact hE.1.trans (by linarith)
  have hLayers (i : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (E.basis.repr (a j : H) k) ≤ p + (p + 3) ^ 8 := by
    let j := i.val + 1
    have hj : 1 ≤ j := Nat.le_add_left 1 _
    by_cases hjs : j ≤ s
    · obtain ⟨a₀, ha₀⟩ := hfast j hj hjs
      obtain ⟨a, ha⟩ := exists_rankOneFastLayer_basis D R W hs hR j hjs a₀ ha₀
      have hle : rankOneFastLayer D R W j ≤ H.toSubmodule := by
        change rankOneFastLayer D R W j ≤ D.filtration.gradedRefiltrationLayer W 1
        rw [← rankOneFastLayer_one D R W]
        exact rankOneFastLayer_antitone D R W hj
      let e : F.layer j ≃ₗ[ℚ] rankOneFastLayer D R W j := Submodule.comapSubtypeEquivOfLe hle
      let a' := (a.map e.symm).reindex (finCongr e.finrank_eq.symm)
      have hval (u) : ((a' u : H) : L) = (a ((finCongr e.finrank_eq.symm).symm u) : L) := by
        simp only [a', Basis.reindex_apply, Basis.map_apply, e]
        rfl
      refine ⟨a', fun u k => ?_⟩
      apply LE.le.trans _ hqp
      apply rationalLogHeight_le_of_height
        (embedding_basis_coordinate_height E.basis D.basis H.incl.toLinearMap
          (fun _ _ h => Subtype.ext h) hA (fun z u => rationalHeightLE_ceil_exp (hinc u z))
          (a' u : H) (K := A) (fun z => by
            change RationalHeightLE (D.basis.repr ((a' u : H) : L) z) A
            rw [hval]
            exact rationalHeightLE_ceil_exp (ha _ z)) k)
      simpa only [show p + 1 + 2 = p + 3 by ring] using
        embedding_coordinate_height_budget _ _ A A hp₁ hd hH hAp hAp
    · have hi : i.val + 1 = s + 1 := by dsimp [j] at hjs; omega
      have heq : F.layer (i.val + 1) = E.filtration.layer (i.val + 1) := by
        rw [hi, F.terminal, E.filtration.terminal]
      rw [heq]
      exact ⟨E.layerBasis i, fun u k => (hE.2.2.2 i u k).trans hpq⟩
  choose a ha using hLayers
  let E' : RationalFilteredNilmanifold H s (finrank ℚ H) :=
    { filtration := F
      basis := E.basis
      layerBasis := a
      lattice := E.lattice
      grid := E.grid
      grid_pos := E.grid_pos
      inner_grid := E.inner_grid
      outer_grid := E.outer_grid }
  exact ⟨E', rfl, rfl, rfl, hE.1.trans hpq, hE.2.1.trans (Real.exp_le_exp.mpr hpq),
    (fun i j k => (hE.2.2.1 i j k).trans hpq), ha⟩

/-- The actual BCH product of the rank-two and fast factors has its
positive-degree log coefficients in the enlarged layers. -/
theorem rankOneFast_product_coefficients (hs : 1 ≤ s)
    (K U : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hK : ∀ j : Fin s, coefficients K.log (Finsupp.single () (j.val + 1)) ∈
      (R.filtration.layer (j.val + 1) 2).baseChange ℝ)
    (hU : ∀ j : Fin s, coefficients U.log (Finsupp.single () (j.val + 1)) ∈
      D.filtration.realGradedRefiltrationLayer W (j.val + 1)) :
    ∀ j : Fin s, coefficients (K * U).log (Finsupp.single () (j.val + 1)) ∈
      (rankOneFastLayer D R W (j.val + 1)).baseChange ℝ := by
  intro j
  let α : Unit →₀ ℕ := Finsupp.single () (j.val + 1)
  have hBCH := R.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs (fun _ : Unit => 1) α K U
  simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one] at hBCH
  have hRle : (R.filtration.layer (j.val + 1) 2).baseChange ℝ ≤
      (rankOneFastLayer D R W (j.val + 1)).baseChange ℝ :=
    Submodule.baseChange_mono ℝ le_sup_right
  have hUle : D.filtration.realGradedRefiltrationLayer W (j.val + 1) ≤
      (rankOneFastLayer D R W (j.val + 1)).baseChange ℝ :=
    Submodule.baseChange_mono ℝ le_sup_left
  have hsum := Submodule.add_mem ((rankOneFastLayer D R W (j.val + 1)).baseChange ℝ)
    (hRle hBCH) (Submodule.add_mem _ (hRle (hK j)) (hUle (hU j)))
  simpa only [sub_add_cancel] using hsum

/-- Lift the actual normalized residual product to the enlarged filtration,
with its integer evaluations unchanged by the inclusion. -/
theorem exists_rankOneFast_product_orbit (hs : 1 ≤ s)
    (K U : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hK₀ : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1)
    (hU₀ : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1)
    (hK : ∀ j : Fin s, coefficients K.log (Finsupp.single () (j.val + 1)) ∈
      (R.filtration.layer (j.val + 1) 2).baseChange ℝ)
    (hU : ∀ j : Fin s, coefficients U.log (Finsupp.single () (j.val + 1)) ∈
      D.filtration.realGradedRefiltrationLayer W (j.val + 1)) :
    let F := rankOneFastFiltration D R W
    let Φ := realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
    ∃ g : F.realification.PolynomialOrbit (fun _ : Unit => 1),
      ∀ x : Unit → ℤ, Φ (F.realification.polynomialOrbitEval (fun _ : Unit => 1) x g) =
        D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (K * U) := by
  intro F Φ
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let w : Unit → ℕ := fun _ => 1
  let α (i : Fin s) : Unit →₀ ℕ := Finsupp.single () (i.val + 1)
  let a (i : Fin s) := coefficients (K * U).log (α i)
  have ha := rankOneFast_product_coefficients D R W hs K U hK hU
  have hH (i : Fin s) : a i ∈ H.toSubmodule.baseChange ℝ := by
    change a i ∈ (D.filtration.gradedRefiltrationLayer W 1).baseChange ℝ
    rw [← rankOneFastLayer_one D R W]
    exact Submodule.baseChange_mono ℝ (rankOneFastLayer_antitone D R W (by omega)) (ha i)
  let c (i : Fin s) : H.toSubmodule.baseChange ℝ := ⟨a i, hH i⟩
  let b (i : Fin s) : ℝ ⊗[ℚ] H := (realificationSubmoduleEquiv H.toSubmodule).symm (c i)
  have hb (i : Fin s) : inc (b i) = a i :=
    congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply (c i))
  have hadapt : F.realification.Adapted w (positiveUnivariate b) := by
    apply (F.realification.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro i
    have hw : Finsupp.weight w (α i) = i.val + 1 := by
      simp only [α, w, Finsupp.weight_single, smul_eq_mul, mul_one]
    change b i ∈ ((rankOneFastLayer D R W (Finsupp.weight w (α i))).comap
      H.incl.toLinearMap).baseChange ℝ
    rw [hw, realification_comap]
    change inc (b i) ∈ (rankOneFastLayer D R W (i.val + 1)).baseChange ℝ
    rw [hb]
    exact ha i
  let g := polynomialOrbitOfLog (positiveUnivariate b) hadapt
  have hg0 : D.filtration.realification.polynomialOrbitEval w 0 (K * U) = 1 := by
    rw [map_mul, hK₀, hU₀, one_mul]
  have hzero := congrArg NilpotentLieBCHGroup.coord hg0
  change eval (fun _ : Unit => (0 : ℚ)) (K * U).log = 0 at hzero
  rw [eval_zero_eq_coefficient] at hzero
  have hmap : VectorPolynomial.map inc g.log = (K * U).log := by
    apply coefficients.injective
    apply Finsupp.ext
    intro β
    rw [coefficients_map]
    change inc (coefficients (positiveUnivariate b) β) = coefficients (K * U).log β
    by_cases hβ : ∃ i : Fin s, α i = β
    · obtain ⟨i, rfl⟩ := hβ
      rw [positiveUnivariate_coefficient, hb]
    · rw [positiveUnivariate_coefficient_eq_zero b β (not_exists.mp hβ), map_zero]
      let j := β ()
      have hj : Finsupp.single () j = β := by
        apply Finsupp.ext
        intro i
        cases i
        exact Finsupp.single_eq_same
      by_cases hj0 : j = 0
      · rw [← hj, hj0, Finsupp.single_zero, hzero]
      have hjs : s < j := by
        by_contra! hjs
        let i : Fin s := ⟨j - 1, by omega⟩
        have hi : i.val + 1 = j := by
          change (j - 1) + 1 = j
          omega
        exact hβ ⟨i, by simpa only [α, hi] using hj⟩
      have hmem := (D.filtration.realification.adapted_iff_coefficients _ _).mp (K * U).adapted β
      have hw : Finsupp.weight w β = j := by
        rw [← hj, Finsupp.weight_single, smul_eq_mul]
        simp only [w, mul_one]
      rw [hw, D.filtration.realification.layer_eq_bot_above_step hjs, Submodule.mem_bot] at hmem
      exact hmem.symm
  refine ⟨g, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  change inc (eval (fun i => (x i : ℚ)) g.log) = eval (fun i => (x i : ℚ)) (K * U).log
  rw [← hmap, eval_map]

/-- The inclusion of the enlarged model preserves top-layer membership
and annihilates the frequency whenever it annihilates the original fast top. -/
theorem rankOneFast_top_annihilation (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ D.filtration.realGradedRefiltrationLayer W s, realifyFunctional η x = 0) :
    let Φ := realificationMap (hnil := (rankOneFastFiltration D R W).lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
    ∀ z ∈ (rankOneFastFiltration D R W).realification.subgroup s,
      Φ z ∈ D.filtration.realification.subgroup s ∧ realifyFunctional η (Φ z).coord = 0 := by
  intro Φ z hz
  have hzLayer : z.coord ∈ (rankOneFastFiltration D R W).realification.layer s := hz
  change z.coord ∈ ((rankOneFastLayer D R W s).comap
    (D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ at hzLayer
  rw [realification_comap, rankOneFastLayer_top] at hzLayer
  have htop : (Φ z).coord ∈ D.filtration.realGradedRefiltrationLayer W s := hzLayer
  exact ⟨D.filtration.realGradedRefiltrationLayer_le W s htop, hη _ htop⟩

end

end PrimeUniformity
