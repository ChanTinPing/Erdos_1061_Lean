import PrimeUniformity.UpstreamTypeIRowRecovery
import PrimeUniformity.UpstreamTypeICoefficientLift
import PrimeUniformity.UpstreamTypeIRankReassembly

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped BigOperators TensorProduct

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
/-- Recover a normalized Type I orbit factorization from the projected row
constraints on a common dense set of dilations. The common rational grid
is the product of the bounded denominators of the individual degree lifts. -/
theorem exists_typeI_rank_two_orbits_of_projected_rows
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r n : ℕ}
    (D : RationalFilteredNilmanifold V s n) (R : D.DegreeRankStructure r) (hs : 1 ≤ s)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ω : Fin n → ℕ)
    (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (η : ∀ j, V →ₗ[ℚ] (J j → ℚ))
    (hker : ∀ j, LinearMap.ker (η j) = D.filtration.gradedRefiltrationLayer W (j.val + 1) ⊔
      R.filtration.layer (j.val + 1) 2)
    (row : ∀ (j : Fin s), J j → (Fin 4 → R.filtration.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial (j.val + 1)))) →ₗ[ℚ] ℚ)
    (m : ∀ j, J j → ℕ) (hm : ∀ j i, 0 < m j i)
    (L cutoff : ℕ) {ρ H X p : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X)
    (hRρ : 16 ≤ ρ * cutoff) (hfreq : 16 * (cutoff : ℝ) * H ≤ X / L)
    (hden : ∀ j : Fin s,
      ((cutoff * WeylInverse.leadingInverseBudget (j.val + 1) cutoff : ℕ) : ℝ) * H ≤ X / L)
    (S : Finset ℕ) (hS : S ⊆ dyadicDilationInterval L)
    (hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ))
    {B : ℕ} (hB : 1 ≤ B) (hheight : ∀ j i k, RationalHeightLE (η j (D.basis i) k) B)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p) (hX : Real.exp (separationBudget p) ≤ X) :
    let w : Unit → ℕ := fun _ => 1
    let G := R.filtration
    let F := G.associatedDegree
    let hF' : ∀ d, F.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}) := fun d =>
      (congrArg (fun M : NilpotentLieFiltration V s => M.layer d) R.associated).trans (hF d)
    let gRank : F.realification.PolynomialOrbit w := R.orbitEquiv w g
    let readRow (j : Fin s) (i : J j) := projectedHorizontalRow G F typeISingleSlot
      (typeISingleSlot_mem_rankOne G) w (typeIMonomial (j.val + 1)) (row j i)
      (F.realSymbolOfPolynomial D.basis ω hF' w gRank.log)
    let Q (u : Σ j : Fin s, J j) := typeIRowDenominatorBound cutoff (u.1.val + 1) ρ * m u.1 u.2
    ((↑(∏ u, Q u) : ℝ) ≤ Real.exp p) →
    (∀ j : Fin s, (↑(∏ u, Q u) : ℝ) * typeIRowErrorBound cutoff (j.val + 1) ρ H ≤ Real.exp p) →
    (∀ j i, readRow j i = realifyCoordinateMap (η j)
      (coefficients gRank.log (Finsupp.single () (j.val + 1))) i) →
    (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
      |((m j i : ℝ) * readRow j i) * (d : ℝ) ^ (j.val + 1) - a| ≤ H / (X / L) ^ (j.val + 1)) →
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
  classical
  intro w G F hF' gRank readRow Q hQ herror heq hnear
  have hglog : gRank.log = g.log := R.orbitEquiv_log w g
  let θ (j : Fin s) (i : J j) := realifyCoordinateMap (η j)
    (coefficients g.log (Finsupp.single () (j.val + 1))) i
  have hrowEq (j : Fin s) (i : J j) : readRow j i = θ j i := by
    simpa only [θ, hglog] using heq j i
  have hnearθ (d : ℕ) (hd : d ∈ S) (j : Fin s) (i : J j) : ∃ a : ℤ,
      |((m j i : ℝ) * θ j i) * (d : ℝ) ^ (j.val + 1) - a| ≤ H / (X / L) ^ (j.val + 1) := by
    obtain ⟨a, ha⟩ := hnear d hd j i
    rw [hrowEq j i] at ha
    exact ⟨a, ha⟩
  obtain ⟨l, hl, hlQ, a, ha⟩ := recover_typeI_coefficient_rows θ m hm
    L cutoff hL hρ hH hLX hRρ hfreq hden S hS hdense hnearθ
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlp : (l : ℝ) ≤ Real.exp p := (Nat.cast_le.mpr hlQ).trans hQ
  have hnearG (j : Fin s) (i : J j) :
      |(l : ℝ) * realifyCoordinateMap (η j)
        (coefficients g.log (Finsupp.single () (j.val + 1))) i - (a j i : ℝ)| ≤
          Real.exp p / X ^ (j.val + 1) := by
    exact (ha j i).trans (div_le_div_of_nonneg_right (herror j) (pow_nonneg hXpos.le _))
  obtain ⟨q, hq, e, b, he, hb, heBound, hbGrid, hres⟩ :=
    exists_typeI_rank_two_coefficient_lifts D R W ω hF η hker hB hl hheight
      hp hn hJ hBp hlp hX g a hnearG
  obtain ⟨hMpos, _, ε, K, U, γ, _, _, hε0, hK0, hU0, hγ0, hε, hγ, hprod, hKU⟩ :=
    exists_typeI_rank_two_reassembly D R hs g hg W e b he hb hXpos (Real.exp_pos _).le
      heBound q (fun j => (hq j).1) hbGrid hres
  have hM : ((∏ j, q j : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * (p + 2) ^ 36) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin s, Real.exp ((p + 2) ^ 36) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg (q j)) (fun j _ => (hq j).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  exact ⟨∏ j, q j, hMpos, hM, ε, K, U, γ, hε0, hK0, hU0, hγ0, hε, hγ, hprod, hKU⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeI_rank_two_orbits_of_projected_rows
