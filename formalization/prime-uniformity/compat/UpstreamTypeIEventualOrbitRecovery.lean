import PrimeUniformity.TypeIDilationBudget
import PrimeUniformity.UpstreamTypeICoefficientLift
import PrimeUniformity.UpstreamTypeIRankReassembly

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

/-- Uniform Type I rank-two factorization from a dense family of ambient
row estimates. A single logarithmic budget bounds the rows, clearing
denominators, density loss and error at the sampled scale. -/
theorem exists_uniform_native_typeI_orbits_of_dense_rows (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {V : Type} [LieRing V] [LieAlgebra ℚ V] {r n : ℕ}
        (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r)
        (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ω : Fin n → ℕ)
        (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
        (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1 →
      ∀ {J : Fin s → Type} [∀ j, Fintype (J j)] (η : ∀ j, V →ₗ[ℚ] (J j → ℚ)),
      (∀ j, LinearMap.ker (η j) = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔
        R.filtration.layer (j.val + 1) 2) →
      ∀ (B : ℕ), 1 ≤ B → (∀ j i k, RationalHeightLE (η j (D.basis i) k) B) →
      ∀ (m : ∀ j, J j → ℕ), (∀ j i, 0 < m j i) → ∀ (L : ℕ) {t H X₀ X : ℝ},
      1 ≤ t → 0 ≤ H → H ≤ Real.exp t → (∀ j i, (m j i : ℝ) ≤ Real.exp t) →
      (n : ℝ) ≤ t → (B : ℝ) ≤ Real.exp t → (Fintype.card ((Σ j : Fin s, J j) × Bool) : ℝ) ≤ t →
      0 < L → Real.exp ((C : ℝ) * t) ≤ X₀ / L → 0 < X → X * Real.exp (-t) ≤ X₀ →
      Real.exp (separationBudget ((C : ℝ) * t ^ 2)) ≤ X →
      ∀ (S : Finset ℕ), S ⊆ dyadicDilationInterval L →
      Real.exp (-t) * ((dyadicDilationInterval L).card : ℝ) ≤ S.card →
      (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * realifyCoordinateMap (η j)
          (coefficients g.log (Finsupp.single () (j.val + 1))) i) * (d : ℝ) ^ (j.val + 1) - a| ≤
            H / (X₀ / L) ^ (j.val + 1)) →
      let w : Unit → ℕ := fun _ => 1
      let p := (C : ℝ) * t ^ 2
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) ∧
        ∃ ε K U γ : D.filtration.realification.PolynomialOrbit w,
          D.filtration.realification.polynomialOrbitEval w 0 ε = 1 ∧
          D.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧
          D.filtration.realification.polynomialOrbitEval w 0 U = 1 ∧
          D.filtration.realification.polynomialOrbitEval w 0 γ = 1 ∧
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => X)
            (Real.exp ((p + 2) ^ 18 + p)) ε.log ∧
          CoefficientGrid (D.basis.baseChange ℝ) M γ.log ∧ ε * K * U * γ = g ∧
          ∀ j : Fin s,
            coefficients K.log (Finsupp.single () (j.val + 1)) ∈
              (R.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
            coefficients U.log (Finsupp.single () (j.val + 1)) ∈
              (D.filtration.gradedRefiltrationLayer W (j.val + 1)).baseChange ℝ := by
  obtain ⟨C, hC, hScalar⟩ := exists_uniform_typeI_coefficient_recovery s
  refine ⟨C, hC, ?_⟩
  intro V _ _ r n D R W ω hF g hg J _ η hker B hB hheight m hm L t H X₀ X ht hH hHt hmt hn hBt hcard
    hL hside hX hX₀ hXlift S hS hdense hnear w p
  let θ (j : Fin s) (i : J j) := realifyCoordinateMap (η j)
    (coefficients g.log (Finsupp.single () (j.val + 1))) i
  obtain ⟨l, hl, hlp, hrows⟩ := hScalar θ m hm L ht hH hHt hmt hcard hL hside hX hX₀ S hS hdense hnear
  choose a ha using hrows
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have ht2 : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
  have htp : t ≤ p := ht2.trans (by
    change t ^ 2 ≤ (C : ℝ) * t ^ 2
    exact le_mul_of_one_le_left (sq_nonneg t) (by exact_mod_cast hC))
  have hJ (j : Fin s) : (Fintype.card (J j) : ℝ) ≤ p := by
    have hc : Fintype.card (J j) ≤ Fintype.card ((Σ d : Fin s, J d) × Bool) := by
      rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sigma]
      exact (Finset.single_le_sum (f := fun i : Fin s => Fintype.card (J i))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
        (Nat.le_mul_of_pos_right _ (by decide : 0 < (2 : ℕ)))
    exact ((Nat.cast_le.mpr hc).trans hcard).trans htp
  have hBp : (B : ℝ) ≤ Real.exp p := hBt.trans (Real.exp_le_exp.mpr htp)
  obtain ⟨q, hq, e, b, he, hb, heBound, hbGrid, hres⟩ :=
    exists_typeI_rank_two_coefficient_lifts D R W ω hF η hker hB hl hheight
      (ht₀.trans htp) (hn.trans htp) hJ hBp hlp hXlift g a ha
  obtain ⟨hMpos, _, ε, K, U, γ, _, _, hε0, hK0, hU0, hγ0, hε, hγ, hprod, hKU⟩ :=
    exists_typeI_rank_two_reassembly D R hs g hg W e b he hb hX (Real.exp_pos _).le
      heBound q (fun j => (hq j).1) hbGrid hres
  have hM : ((∏ j, q j : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin s, Real.exp ((p + 2) ^ 36) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg (q j)) (fun j _ => (hq j).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  exact ⟨∏ j, q j, hMpos, hM, ε, K, U, γ, hε0, hK0, hU0, hγ0, hε, hγ, hprod, hKU⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_uniform_native_typeI_orbits_of_dense_rows
