import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
import OAI.Combinatorics.Progressions.Estimates.RealAnnihilatorCorrections
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
import OAI.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization
import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

namespace PrimeUniformity

open OAI.Erdos3 OAI.Erdos3.NilpotentLieFiltration
open Module Matrix VectorPolynomial
open scoped BigOperators Matrix TensorProduct

/-- Lift a finite family of near-integer row coordinates inside a layer
spanned by a subset of the ambient basis. The image section also works
when the rows are dependent on that layer. -/
theorem exists_typeI_layer_coefficient_lifts
    {ι J V : Type*} [Fintype ι] [Fintype J] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (P Q : Submodule ℚ V) (S : Set ι)
    (hP : P = Submodule.span ℚ (b '' S))
    (η : V →ₗ[ℚ] (J → ℚ)) (hker : LinearMap.ker η = Q)
    {B l k : ℕ} (hB : 1 ≤ B) (hl : 0 < l) (hk : 0 < k)
    (hheight : ∀ i j, RationalHeightLE (η (b i) j) B)
    {p X : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hJ : (Fintype.card J : ℝ) ≤ p) (hBp : (B : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (hX : Real.exp (separationBudget p) ≤ X)
    (x : ℝ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℝ) (a : J → ℤ)
    (hnear : ∀ j, |(l : ℝ) * realifyCoordinateMap η x j - (a j : ℝ)| ≤ Real.exp p / X ^ k) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ e q : ℝ ⊗[ℚ] V,
        e ∈ P.baseChange ℝ ∧ q ∈ P.baseChange ℝ ∧
        ‖(b.baseChange ℝ).equivFun e‖ ≤ Real.exp ((p + 2) ^ 18 + p) / X ^ k ∧
        (b.baseChange ℝ).equivFun q ∈ realDenominatorGrid m ∧
        x - (e + q) ∈ Q.baseChange ℝ := by
  classical
  let bR := b.baseChange ℝ
  let PR := P.baseChange ℝ
  have hPR : PR = Submodule.span ℝ (bR '' S) := by
    dsimp only [PR]
    rw [hP, Submodule.baseChange_span, Set.image_image]
    congr 2
    funext i
    exact (Basis.baseChange_apply ℝ b i).symm
  let c := supportedSubmoduleBasis bR PR S hPR
  let lift : (S → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V) := PR.subtype.comp c.equivFun.symm.toLinearMap
  let A : Matrix J S ℚ := fun j i => η (b i) j
  let Ar : Matrix J S ℝ := fun j i => (A j i : ℝ)
  have hEvalLin : (realifyCoordinateMap η).comp lift = Matrix.mulVecLin Ar := by
    apply (Pi.basisFun ℝ S).ext
    intro i
    rw [Pi.basisFun_apply]
    change realifyCoordinateMap η ((c.equivFun.symm (Pi.single i 1) : PR) : ℝ ⊗[ℚ] V) =
      Ar *ᵥ Pi.single i 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one]
    funext j
    change realifyCoordinateMap η ((c i : PR) : ℝ ⊗[ℚ] V) j = (A j i : ℝ)
    rw [supportedSubmoduleBasis_coe, Basis.baseChange_apply, realifyCoordinateMap_tmul, one_mul]
  have hEval (u : S → ℝ) : realifyCoordinateMap η (lift u) = Ar *ᵥ u :=
    (DFunLike.congr_fun hEvalLin u).trans (Matrix.mulVecLin_apply _ _)
  have hcoord (u : S → ℝ) (i : ι) :
      bR.equivFun (lift u) i = if hi : i ∈ S then u ⟨i, hi⟩ else 0 := by
    let y := c.equivFun.symm u
    by_cases hi : i ∈ S
    · rw [dite_eq_left hi]
      change bR.repr (y : ℝ ⊗[ℚ] V) i = u ⟨i, hi⟩
      rw [← supportedSubmoduleBasis_repr bR PR S hPR y ⟨i, hi⟩]
      exact congrFun (c.equivFun.apply_symm_apply u) ⟨i, hi⟩
    · rw [dite_eq_right hi]
      change bR.repr (y : ℝ ⊗[ℚ] V) i = 0
      exact (basis_mem_span_image_iff bR S y.val).mp (hPR ▸ y.property) i hi
  let α : Unit →₀ ℕ := Finsupp.single () k
  have hα : α ≠ 0 := by
    intro h
    have hh := congrArg (fun β : Unit →₀ ℕ => β ()) h
    exact hk.ne' (by simpa only [α, Finsupp.single_eq_same, Finsupp.zero_apply] using hh)
  have hscale : monomialScale (fun _ : Unit => X) α = X ^ k :=
    Finsupp.prod_single_index (a := ()) (b := k) (h := fun _ d => X ^ d) (pow_zero X)
  have hX' : 0 < X := (Real.exp_pos _).trans_le hX
  have hS : (Fintype.card S : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)).trans hι
  obtain ⟨C, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting A hB hl
    (fun j i => hheight i j) hp hJ hS hBp hlp (fun _ : Unit => X) (fun _ => hX)
  let vx := c.equivFun (⟨x, hx⟩ : PR)
  have hxLift : lift vx = x := by simp [lift, vx]
  let bq : J → ℝ := fun j => (a j : ℝ) / l
  let ae := realifyCoordinateMap η x - bq
  have hlR : 0 < (l : ℝ) := Nat.cast_pos.mpr hl
  have hbq : bq ∈ realDenominatorGrid l := by
    refine ⟨a, ?_⟩
    funext j
    change (a j : ℝ) = (l : ℝ) * ((a j : ℝ) / l)
    field_simp [hlR.ne']
  have hae : ‖ae‖ ≤ Real.exp p / monomialScale (fun _ : Unit => X) α := by
    rw [hscale]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    rw [Real.norm_eq_abs]
    change |realifyCoordinateMap η x j - (a j : ℝ) / l| ≤ _
    have heq : realifyCoordinateMap η x j - (a j : ℝ) / l =
        ((l : ℝ) * realifyCoordinateMap η x j - (a j : ℝ)) / l := by
      field_simp [hlR.ne']
    rw [heq, abs_div, abs_of_pos hlR, div_le_iff₀ hlR]
    exact (hnear j).trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hl))
  have hsum : Ar *ᵥ vx = ae + bq := by
    rw [← hEval, hxLift]
    simp [ae]
  obtain ⟨_, _, he, hq, hz⟩ := hsolve α hα ae bq vx hae hbq hsum
  let ec := (fun i j => (C i j : ℝ)) *ᵥ ae
  let qc := (fun i j => (C i j : ℝ)) *ᵥ bq
  refine ⟨m, hm, hmp, lift ec, lift qc, (c.equivFun.symm ec).property,
    (c.equivFun.symm qc).property, ?_, ?_, ?_⟩
  · rw [hscale] at he
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [hcoord]
    by_cases hi : i ∈ S
    · rw [dite_eq_left hi]
      exact (norm_le_pi_norm ec ⟨i, hi⟩).trans he
    · rw [dite_eq_right hi, norm_zero]
      positivity
  · obtain ⟨z, hz⟩ := hq
    refine ⟨fun i => if hi : i ∈ S then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    change ((if hi : i ∈ S then z ⟨i, hi⟩ else 0 : ℤ) : ℝ) = (m : ℝ) * bR.equivFun (lift qc) i
    rw [hcoord]
    by_cases hi : i ∈ S
    · simpa only [dite_eq_left hi, qc, Pi.smul_apply, smul_eq_mul] using congrFun hz ⟨i, hi⟩
    · simp [hi]
  · have hr : x - (lift ec + lift qc) = lift (vx - ec - qc) := by
      rw [map_sub, map_sub, hxLift]
      abel
    rw [hr, ← hker, mem_realified_coordinate_kernel_iff_eq_zero, hEval]
    exact hz

set_option maxHeartbeats 1000000 in
/-- Apply the layer lift to the positive-degree coefficients of one native
orbit. The resulting coefficient families supply the smooth, rational,
and quotient-kernel hypotheses of rank-two reassembly. -/
theorem exists_typeI_rank_two_coefficient_lifts
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
    (D : RationalFilteredNilmanifold L s n) (R : D.DegreeRankStructure r)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ω : Fin n → ℕ)
    (hF : ∀ d, D.filtration.layer d = Submodule.span ℚ (D.basis '' {i | d ≤ ω i}))
    {J : Fin s → Type*} [∀ d, Fintype (J d)]
    (η : ∀ d, L →ₗ[ℚ] (J d → ℚ))
    (hker : ∀ d, LinearMap.ker (η d) = D.filtration.gradedRefiltrationLayer W (d.val + 1) ⊔
      R.filtration.layer (d.val + 1) 2)
    {B l : ℕ} (hB : 1 ≤ B) (hl : 0 < l)
    (hheight : ∀ d i j, RationalHeightLE (η d (D.basis i) j) B)
    {p X : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hJ : ∀ d, (Fintype.card (J d) : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (hX : Real.exp (separationBudget p) ≤ X)
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (a : ∀ d, J d → ℤ)
    (hnear : ∀ d j, |(l : ℝ) * realifyCoordinateMap (η d)
        (coefficients g.log (Finsupp.single () (d.val + 1))) j - (a d j : ℝ)| ≤
          Real.exp p / X ^ (d.val + 1)) :
    ∃ m : Fin s → ℕ, (∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp ((p + 2) ^ 36)) ∧
      ∃ e q : Fin s → ℝ ⊗[ℚ] L,
        (∀ d, e d ∈ D.filtration.realification.layer (d.val + 1)) ∧
        (∀ d, q d ∈ D.filtration.realification.layer (d.val + 1)) ∧
        (∀ d, ‖(D.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp ((p + 2) ^ 18 + p) / X ^ (d.val + 1)) ∧
        (∀ d, (D.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d)) ∧
        ∀ d, coefficients g.log (Finsupp.single () (d.val + 1)) - (e d + q d) ∈
          (D.filtration.gradedRefiltrationLayer W (d.val + 1) ⊔
            R.filtration.layer (d.val + 1) 2).baseChange ℝ := by
  have hx (d : Fin s) : coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.filtration.layer (d.val + 1)).baseChange ℝ := by
    change coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      D.filtration.realification.layer (d.val + 1)
    have h := (D.filtration.realification.adapted_iff_coefficients _ _).mp g.adapted
      (Finsupp.single () (d.val + 1))
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
  have hι : (Fintype.card (Fin n) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hn
  have hlift (d : Fin s) := exists_typeI_layer_coefficient_lifts
    (ι := Fin n) (J := J d) (V := L) D.basis
    (D.filtration.layer (d.val + 1))
    (D.filtration.gradedRefiltrationLayer W (d.val + 1) ⊔ R.filtration.layer (d.val + 1) 2)
    {i | d.val + 1 ≤ ω i} (hF (d.val + 1)) (η d) (hker d)
    hB hl (Nat.succ_pos d.val) (hheight d) hp hι (hJ d) hBp hlp hX
    (coefficients g.log (Finsupp.single () (d.val + 1))) (hx d) (a d) (hnear d)
  choose m hm hmp e q he hq heBound hqGrid hres using hlift
  refine ⟨m, fun d => ⟨hm d, hmp d⟩, e, q, ?_, ?_, heBound, hqGrid, hres⟩
  · intro d
    exact he d
  · intro d
    exact hq d

end PrimeUniformity

#print axioms PrimeUniformity.exists_typeI_layer_coefficient_lifts
#print axioms PrimeUniformity.exists_typeI_rank_two_coefficient_lifts
