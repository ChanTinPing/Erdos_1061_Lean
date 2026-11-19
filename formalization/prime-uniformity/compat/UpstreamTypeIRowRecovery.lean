import PrimeUniformity.DilationDescent
import PrimeUniformity.UpstreamTypeIRowLift

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped Classical BigOperators Polynomial TensorProduct

private noncomputable def typeIRowSeparationThreshold (R k : ℕ) (ρ : ℝ) : ℝ :=
  let B := WeylInverse.leadingInverseBudget k R * 2 ^ k + 1
  8 * (2 * (B : ℝ) + 3) * ((k : ℝ) + 1) / ρ

noncomputable def typeIRowDenominatorBound (R k : ℕ) (ρ : ℝ) : ℕ :=
  max ((R * WeylInverse.leadingInverseBudget k R) ^ 2) (⌈typeIRowSeparationThreshold R k ρ⌉₊ ^ k)

noncomputable def typeIRowErrorBound (R k : ℕ) (ρ H : ℝ) : ℝ :=
  let D := WeylInverse.leadingInverseBudget k R
  let K := typeIRowSeparationThreshold R k ρ
  let C := ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k * ((k : ℝ) + 1) * K ^ k
  max C (K ^ k) * H

/-- Recover every unscaled coefficient from its estimates on the same dense
dyadic set. Each row's clearing multiplier is included in its recovered
denominator before taking the common product. -/
theorem recover_typeI_coefficient_rows {s : ℕ} {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (θ : ∀ j, J j → ℝ) (m : ∀ j, J j → ℕ) (hm : ∀ j i, 0 < m j i)
    (L R : ℕ) {ρ H X : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X)
    (hRρ : 16 ≤ ρ * R) (hfreq : 16 * (R : ℝ) * H ≤ X / L)
    (hden : ∀ j : Fin s,
      ((R * WeylInverse.leadingInverseBudget (j.val + 1) R : ℕ) : ℝ) * H ≤ X / L)
    (S : Finset ℕ) (hS : S ⊆ dyadicDilationInterval L)
    (hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ))
    (hnear : ∀ d ∈ S, ∀ j i, ∃ a : ℤ,
      |((m j i : ℝ) * θ j i) * (d : ℝ) ^ (j.val + 1) - a| ≤ H / (X / L) ^ (j.val + 1)) :
    let B (u : Σ j : Fin s, J j) := typeIRowDenominatorBound R (u.1.val + 1) ρ * m u.1 u.2
    ∃ q : ℕ, 0 < q ∧ q ≤ (∏ u, B u) ∧ ∃ a : ∀ j, J j → ℤ,
      ∀ j i, |(q : ℝ) * θ j i - (a j i : ℝ)| ≤
        ((↑(∏ u, B u) : ℝ) * typeIRowErrorBound R (j.val + 1) ρ H) /
          X ^ (j.val + 1) := by
  classical
  intro B
  have hindividual (u : Σ j : Fin s, J j) : ∃ q : ℕ, ∃ a : ℤ,
      0 < q ∧ q ≤ B u ∧ |(q : ℝ) * θ u.1 u.2 - a| ≤
        typeIRowErrorBound R (u.1.val + 1) ρ H / X ^ (u.1.val + 1) := by
    obtain ⟨j, i⟩ := u
    let k := j.val + 1
    let p : ℝ[X] := Polynomial.monomial k ((m j i : ℝ) * θ j i)
    have hcoeff : p.coeff k = (m j i : ℝ) * θ j i := Polynomial.coeff_monomial_same _ _
    have hgood : ρ * ((dyadicDilationInterval L).card : ℝ) ≤
        (((dyadicDilationInterval L).filter (fun d : ℕ => ∃ a : ℤ,
          |p.coeff k * (d : ℝ) ^ k - a| ≤ H / (X / L) ^ k)).card : ℝ) := by
      apply hdense.trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro d hd
      exact Finset.mem_filter.mpr ⟨hS hd, by simpa only [hcoeff] using hnear d hd j i⟩
    obtain ⟨q, hq, hqB, a, ha⟩ := recover_single_dilation_dyadic L R hL p
      (Nat.succ_pos j.val) hρ hH hLX hRρ hfreq (hden j) hgood
    refine ⟨q * m j i, a, Nat.mul_pos hq (hm j i), ?_, ?_⟩
    · exact Nat.mul_le_mul_right (m j i) hqB
    · rw [Nat.cast_mul, mul_assoc]
      rw [hcoeff] at ha
      exact ha
  obtain ⟨q, hq, hqB, happrox⟩ := common_denominator_of_bounded_coefficient_estimates
    (fun u : Σ j : Fin s, J j => θ u.1 u.2)
    (fun u => typeIRowErrorBound R (u.1.val + 1) ρ H / X ^ (u.1.val + 1)) B hindividual
  choose a ha using happrox
  exact ⟨q, hq, hqB, fun j i => a ⟨j, i⟩, fun j i => by
    rw [mul_div_assoc]
    exact ha ⟨j, i⟩⟩

/-- Recover the ambient log coordinates of a single Type I orbit from the
projected-symbol inequalities on the common set of dilations. -/
theorem recover_typeI_native_log_rows
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r : ℕ} {ι : Type*}
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (G : DegreeRankLieFiltration V s r) (b : Basis ι ℚ V) (ω : ι → ℕ)
    (hF : ∀ k, G.associatedDegree.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (g : G.associatedDegree.realification.PolynomialOrbit (fun _ : Unit => 1))
    (η : ∀ j, V →ₗ[ℚ] (J j → ℚ))
    (row : ∀ (j : Fin s), J j → (Fin 4 → G.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial (j.val + 1)))) →ₗ[ℚ] ℚ)
    (m : ∀ j, J j → ℕ) (hm : ∀ j i, 0 < m j i)
    (L R : ℕ) {ρ H X : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X)
    (hRρ : 16 ≤ ρ * R) (hfreq : 16 * (R : ℝ) * H ≤ X / L)
    (hden : ∀ j : Fin s,
      ((R * WeylInverse.leadingInverseBudget (j.val + 1) R : ℕ) : ℝ) * H ≤ X / L)
    (S : Finset ℕ) (hS : S ⊆ dyadicDilationInterval L)
    (hdense : ρ * ((dyadicDilationInterval L).card : ℝ) ≤ (S.card : ℝ)) :
    let w : Unit → ℕ := fun _ => 1
    let F := G.associatedDegree
    let θ (j : Fin s) (i : J j) := realifyCoordinateMap (η j)
      (coefficients g.log (Finsupp.single () (j.val + 1))) i
    let readRow (j : Fin s) (i : J j) := projectedHorizontalRow G F typeISingleSlot
      (typeISingleSlot_mem_rankOne G) w (typeIMonomial (j.val + 1)) (row j i)
      (F.realSymbolOfPolynomial b ω hF w g.log)
    (∀ j i, readRow j i = θ j i) →
    (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
      |((m j i : ℝ) * readRow j i) * (d : ℝ) ^ (j.val + 1) - a| ≤ H / (X / L) ^ (j.val + 1)) →
    let B (u : Σ j : Fin s, J j) := typeIRowDenominatorBound R (u.1.val + 1) ρ * m u.1 u.2
    ∃ q : ℕ, 0 < q ∧ q ≤ (∏ u, B u) ∧ ∃ a : ∀ j, J j → ℤ,
      ∀ j i, |(q : ℝ) * θ j i - (a j i : ℝ)| ≤
        ((↑(∏ u, B u) : ℝ) * typeIRowErrorBound R (j.val + 1) ρ H) /
          X ^ (j.val + 1) := by
  intro w F θ readRow heq hnear
  apply recover_typeI_coefficient_rows θ m hm L R hL hρ hH hLX hRρ hfreq hden S hS hdense
  intro d hd j i
  simpa only [heq j i] using hnear d hd j i

/-- Convert the checked Type I factorizations sharing a fast algebra and
grid into the projected row estimates used by dyadic recovery. -/
theorem exists_typeI_projected_rows_of_common_symbol_factors
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s r : ℕ} {ι : Type*} [Fintype ι]
    {J : Fin s → Type*} (G : DegreeRankLieFiltration V s r) (hs : 1 ≤ s)
    (b : Basis ι ℚ V) (ω : ι → ℕ)
    (hF : ∀ k, G.associatedDegree.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (g : G.associatedDegree.realification.PolynomialOrbit (fun _ : Unit => 1))
    (row : ∀ (j : Fin s), J j → (Fin 4 → G.HigherHorizontal
      (Finsupp.weight (fun _ : Unit => 1) (typeIMonomial (j.val + 1)))) →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ G.associatedDegree.AssociatedGraded)
    (p : ℝ) (l : ℕ) (hl : 0 < l) (S : Finset ℕ)
    {T Y : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) {B : ℕ} (hB : 1 ≤ B) :
    let F := G.associatedDegree
    let w : Unit → ℕ := fun _ => 1
    let Xg : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfPolynomial b ω hF w g.log⟩
    (∀ d ∈ S, F.SymbolFactorizationIn b ω hF (fun _ : Unit => T)
      (F.realPolynomialSymbolDilationHom w (d : ℚ) Xg) p l W) →
    (∀ j i,
      G.layerHorizontalImage (F.gradedRefiltrationLayer W) typeISingleSlot
        (fun d x hx => typeISingleSlot_mem_rankOne G d x (F.gradedRefiltrationLayer_le W d hx))
        (Finsupp.weight w (typeIMonomial (j.val + 1))) ≤
          LinearMap.ker (row j i)) →
    (∀ j i (z : SymbolBasisIndex w ω), RationalHeightLE
      (row j i (G.projectedHorizontalSymbolCoefficient F typeISingleSlot
        (typeISingleSlot_mem_rankOne G) w (typeIMonomial (j.val + 1))
        (F.polynomialSymbolBasis b ω hF w z))) B) →
    let N := Fintype.card ι * (s + 1) * 2 ^ s
    let A := B ^ N
    let H := (l : ℝ) * (N : ℝ) * (A : ℝ) * Real.exp p
    ∃ m : ∀ j, J j → ℕ, (∀ j i, 0 < m j i ∧ m j i ≤ A * l) ∧
      ∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * projectedHorizontalRow G F typeISingleSlot (typeISingleSlot_mem_rankOne G)
          w (typeIMonomial (j.val + 1)) (row j i) Xg.coord) * (d : ℝ) ^ (j.val + 1) - a| ≤
            H / Y ^ (j.val + 1) := by
  intro F w Xg hfactor hann hheight N A H
  have hclear (j : Fin s) (i : J j) := exists_typeI_projected_row_integer_columns
    G b ω hF (j.val + 1) (row j i) hB (hheight j i)
  choose c hc hcA hcol using hclear
  refine ⟨fun j i => c j i * l, fun j i => ⟨Nat.mul_pos (hc j i) hl, Nat.mul_le_mul_right _ (hcA j i)⟩, ?_⟩
  intro d hd j i
  obtain ⟨a, ha⟩ := typeI_projected_row_near_integer G hs b ω hF (hY.trans_le hYT) Xg
    d p l W (hfactor d hd) (j.val + 1) (row j i) (hann j i) (c j i) (Nat.cast_nonneg A) (hcol j i)
  refine ⟨a, ha.trans ?_⟩
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hY _)
    (pow_le_pow_left₀ hY.le hYT _)

end PrimeUniformity

#print axioms PrimeUniformity.recover_typeI_coefficient_rows
#print axioms PrimeUniformity.recover_typeI_native_log_rows
#print axioms PrimeUniformity.exists_typeI_projected_rows_of_common_symbol_factors
