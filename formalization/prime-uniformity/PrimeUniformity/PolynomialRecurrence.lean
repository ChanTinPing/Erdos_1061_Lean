module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Polynomial BigOperators
open Polynomial Finset

private theorem int_gap_of_strictMono {n : ℕ} (f : Fin n → ℤ) (hf : StrictMono f)
    {i j : Fin n} (hij : i ≤ j) :
    (j.val : ℤ) - i.val ≤ f j - f i := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have hm : Monotone (fun i : Fin (n + 1) => f i - (i.val : ℤ)) := by
      apply Fin.monotone_iff_le_succ.2
      intro a
      have ha := hf (Fin.castSucc_lt_succ (i := a))
      change f a.castSucc - (a.castSucc.val : ℤ) ≤ f a.succ - (a.succ.val : ℤ)
      simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
        (show f a.castSucc - (a.val : ℤ) ≤ f a.succ - ((a.val : ℤ) + 1) by omega)
    have hij' := hm hij
    change f i - (i.val : ℤ) ≤ f j - (j.val : ℤ) at hij'
    omega

/-- Selecting every `r`-th integer in sorted order gives separated interpolation nodes. -/
theorem exists_separated_integer_nodes (E : Finset ℤ) (d r : ℕ) (h : d * r < E.card) :
    ∃ v : Fin (d + 1) → ℤ, (∀ i, v i ∈ E) ∧
      ∀ i j, i ≠ j → (r : ℤ) ≤ |v i - v j| := by
  let rank (i : Fin (d + 1)) : Fin E.card :=
    ⟨i.val * r, (Nat.mul_le_mul_right r (Nat.le_of_lt_succ i.isLt)).trans_lt h⟩
  let f := E.orderEmbOfFin rfl
  refine ⟨fun i => f (rank i), fun i => E.orderEmbOfFin_mem rfl (rank i), ?_⟩
  have step (i j : Fin (d + 1)) (hij : i < j) : (r : ℤ) ≤ f (rank j) - f (rank i) := by
    have hi : i.val + 1 ≤ j.val := hij
    have hn : i.val * r + r ≤ j.val * r := by
      simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right r hi
    have hle : rank i ≤ rank j := Nat.le_trans (Nat.le_add_right _ _) hn
    have hgap := int_gap_of_strictMono f f.strictMono hle
    have hcast : ((i.val : ℤ) * r) + r ≤ (j.val : ℤ) * r := by exact_mod_cast hn
    change ((j.val * r : ℕ) : ℤ) - ((i.val * r : ℕ) : ℤ) ≤ f (rank j) - f (rank i) at hgap
    simp only [Nat.cast_mul] at hgap
    omega
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [abs_sub_comm]
    exact (step i j hlt).trans (le_abs_self _)
  · exact (step j i hgt).trans (le_abs_self _)

private theorem interpolate_at_separated_nodes {d : ℕ} {N r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (v : Fin (d + 1) → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 N)
    (hsep : ∀ i j, i ≠ j → r ≤ |v i - v j|)
    (p : ℝ[X]) (hp : p.natDegree ≤ d) (hsmall : ∀ i, |p.eval (v i)| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc 0 N) :
    |p.eval x| ≤ (d + 1 : ℕ) * (N / r) ^ d * ε := by
  classical
  have hinj : Function.Injective v := by
    intro i j he
    by_contra hne
    have hh := hsep i j hne
    rw [he, sub_self, abs_zero] at hh
    exact hr.not_ge hh
  have hdeg : p.degree < ((univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast (Nat.lt_succ_of_le hp))
  have hB (i : Fin (d + 1)) : |(Lagrange.basis univ v i).eval x| ≤ (N / r) ^ d := by
    rw [Lagrange.basis, eval_prod, Finset.abs_prod]
    calc
      _ ≤ ∏ j ∈ (univ : Finset (Fin (d + 1))).erase i, N / r := by
        gcongr with j hj
        simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, abs_mul, abs_inv]
        have hsep' := hsep i j (Finset.ne_of_mem_erase hj).symm
        have hdiff : |x - v j| ≤ N :=
          abs_le.mpr ⟨by linarith [hx.1, (hv j).2], by linarith [hx.2, (hv j).1]⟩
        rw [mul_comm, ← div_eq_mul_inv]
        exact div_le_div₀ (hx.1.trans hx.2) hdiff hr hsep'
      _ = _ := by simp [Finset.card_erase_of_mem, div_pow]
  conv_lhs => rw [Lagrange.eq_interpolate hinj.injOn hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  calc
    _ ≤ ∑ i : Fin (d + 1), |(C (p.eval (v i)) * Lagrange.basis univ v i).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (d + 1), ε * (N / r) ^ d := by
      apply Finset.sum_le_sum
      intro i _
      simp only [eval_mul, eval_C, abs_mul]
      exact mul_le_mul (hsmall i) (hB i) (abs_nonneg _) hε
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- A fixed rational grid used for coefficient comparison on the unit interval. -/
noncomputable def interpolationGridNode (d : ℕ) (i : Fin (d + 1)) : ℝ := i.val / (d + 1 : ℕ)

private theorem interpolationGridNode_injective (d : ℕ) : Function.Injective (interpolationGridNode d) := by
  intro i j h
  apply Fin.ext
  have he := (div_left_inj' (by positivity : ((d + 1 : ℕ) : ℝ) ≠ 0)).mp h
  exact_mod_cast he

private theorem interpolationGridNode_mem (d : ℕ) (i : Fin (d + 1)) : interpolationGridNode d i ∈ Set.Icc 0 1 :=
  ⟨by unfold interpolationGridNode; positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast i.isLt.le)⟩

/-- A finite constant controlling coefficients of degree-`d` polynomials on the unit interval. -/
noncomputable def interpolationCoefficientConstant (d : ℕ) : ℝ :=
  1 + ∑ j ∈ range (d + 1), ∑ i : Fin (d + 1), |(Lagrange.basis univ (interpolationGridNode d) i).coeff j|

private theorem coeff_le_of_eval_on_unit {d j : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d)
    (hj : j ≤ d) {H : ℝ} (hH : 0 ≤ H) (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |p.eval x| ≤ H) :
    |p.coeff j| ≤ interpolationCoefficientConstant d * H := by
  classical
  have hdeg : p.degree < ((univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast (Nat.lt_succ_of_le hp))
  conv_lhs => rw [Lagrange.eq_interpolate (interpolationGridNode_injective d).injOn hdeg]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  calc
    _ ≤ ∑ i : Fin (d + 1), |(C (p.eval (interpolationGridNode d i)) * Lagrange.basis univ (interpolationGridNode d) i).coeff j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (d + 1), H * |(Lagrange.basis univ (interpolationGridNode d) i).coeff j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [coeff_C_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (h _ (interpolationGridNode_mem d i)) (abs_nonneg _)
    _ ≤ interpolationCoefficientConstant d * H := by
      rw [← Finset.mul_sum, mul_comm H]
      apply mul_le_mul_of_nonneg_right _ hH
      unfold interpolationCoefficientConstant
      let F (k : ℕ) : ℝ := ∑ i : Fin (d + 1), |(Lagrange.basis univ (interpolationGridNode d) i).coeff k|
      have hF (k : ℕ) : 0 ≤ F k := Finset.sum_nonneg fun i _ => abs_nonneg _
      have hsum : F j ≤ ∑ k ∈ range (d + 1), F k :=
        Finset.single_le_sum (fun k _ => hF k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      exact hsum.trans (le_add_of_nonneg_left zero_le_one)

/-- Small evaluations at separated nodes control each monomial coefficient
at the corresponding inverse length scale. -/
theorem coeff_le_of_separated_evaluations {d j : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d)
    (hj : j ≤ d) {N r ε : ℝ} (hN : 0 < N) (hr : 0 < r) (hε : 0 ≤ ε)
    (v : Fin (d + 1) → ℝ) (hv : ∀ i, v i ∈ Set.Icc 0 N)
    (hsep : ∀ i j, i ≠ j → r ≤ |v i - v j|) (hsmall : ∀ i, |p.eval (v i)| ≤ ε) :
    |p.coeff j| ≤ interpolationCoefficientConstant d * ((d + 1 : ℕ) * (N / r) ^ d * ε) / N ^ j := by
  let q := p.comp (C N * X)
  have hq : q.natDegree ≤ d := by
    have hdeg := natDegree_C_mul_X N hN.ne'
    exact natDegree_comp_le.trans (by rw [hdeg, Nat.mul_one]; exact hp)
  have h := coeff_le_of_eval_on_unit hq hj (by positivity : 0 ≤ (d + 1 : ℕ) * (N / r) ^ d * ε)
    (fun x hx => by
      simp only [q, eval_comp, eval_mul, eval_C, eval_X]
      apply interpolate_at_separated_nodes hr hε v hv hsep p hp hsmall
      exact ⟨mul_nonneg hN.le hx.1, mul_le_of_le_one_right hN.le hx.2⟩)
  have he : q.coeff j = p.coeff j * N ^ j := comp_C_mul_X_coeff
  rw [he, abs_mul, abs_of_nonneg (pow_nonneg hN.le _)] at h
  exact (le_div_iff₀ (pow_pos hN _)).mpr h


/-- Once an integral polynomial leaves a bounded real residual, recurrence close to
integers refines the coefficient errors linearly in the recurrence tolerance.
Only the constant term of the integral polynomial needs to be adjusted. -/
theorem refine_integral_polynomial_approximation {d r B : ℕ} {N ε : ℝ}
    (hN : 0 < N) (hr : 0 < r) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (S : Finset ℤ) (hcount : (2 * B + 3) * (d * r + 1) ≤ S.card)
    (hSN : ∀ n ∈ S, (n : ℝ) ∈ Set.Icc 0 N)
    (p : ℝ[X]) (q : ℤ[X]) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hbound : ∀ n ∈ S, |p.eval (n : ℝ) - ((q.eval n : ℤ) : ℝ)| ≤ B)
    (hnear : ∀ n ∈ S, ∃ z : ℤ, |p.eval (n : ℝ) - z| ≤ ε) :
    ∃ c : ℤ, ∀ j ≤ d, |p.coeff j - (((q + C c).coeff j : ℤ) : ℝ)| ≤
      interpolationCoefficientConstant d * ((d + 1 : ℕ) * (N / r) ^ d * ε) / N ^ j := by
  classical
  let R := p - q.map (Int.castRingHom ℝ)
  have hEval (n : ℤ) : R.eval (n : ℝ) = p.eval (n : ℝ) - ((q.eval n : ℤ) : ℝ) := by
    change (p - q.map (Int.castRingHom ℝ)).eval ((Int.castRingHom ℝ) n) = _
    rw [eval_sub, eval_map_apply]
    rfl
  have hRdeg : R.natDegree ≤ d := (natDegree_sub_le _ _).trans
    (max_le hp (natDegree_map_le.trans hq))
  have hNear (n : ℤ) (hn : n ∈ S) : ∃ z : ℤ, |R.eval (n : ℝ) - z| ≤ ε := by
    obtain ⟨z, hz⟩ := hnear n hn
    refine ⟨z - q.eval n, ?_⟩
    rw [hEval, Int.cast_sub]
    simpa only [sub_sub_sub_cancel_right] using hz
  let label (n : ℤ) : ℤ := if hn : n ∈ S then Classical.choose (hNear n hn) else 0
  have hLabel (n : ℤ) (hn : n ∈ S) : |R.eval (n : ℝ) - label n| ≤ ε := by
    simpa only [label, dif_pos hn] using Classical.choose_spec (hNear n hn)
  let T := Finset.Icc (-(B : ℤ) - 1) ((B : ℤ) + 1)
  have hT : T.card = 2 * B + 3 := by
    simp only [T, Int.card_Icc]
    omega
  have hTne : T.Nonempty := by
    refine ⟨(0 : ℤ), ?_⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hMaps (n : ℤ) (hn : n ∈ S) : label n ∈ T := by
    have hnorm : |(label n : ℝ)| ≤ (B : ℝ) + 1 := by
      calc
        _ = |(label n : ℝ) - R.eval (n : ℝ) + R.eval (n : ℝ)| := by ring_nf
        _ ≤ |(label n : ℝ) - R.eval (n : ℝ)| + |R.eval (n : ℝ)| := abs_add_le _ _
        _ ≤ (1 : ℝ) + B := add_le_add
          (by rw [abs_sub_comm]; exact (hLabel n hn).trans hεone)
          (by rw [hEval]; exact hbound n hn)
        _ = _ := add_comm _ _
    obtain ⟨hlo, hhi⟩ := abs_le.mp hnorm
    have hlo' : (-(B : ℤ) - 1 : ℤ) ≤ label n := by
      exact_mod_cast (show -(B : ℝ) - 1 ≤ (label n : ℝ) by linarith)
    exact Finset.mem_Icc.mpr ⟨hlo', by exact_mod_cast hhi⟩
  have hSize : T.card * (d * r + 1) ≤ S.card := by simpa only [hT] using hcount
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hMaps hTne hSize
  obtain ⟨v, hv, hsep⟩ := exists_separated_integer_nodes
    (S.filter (fun n => label n = c)) d r (Nat.lt_of_succ_le hc)
  let Q := R - C (c : ℝ)
  have hQdeg : Q.natDegree ≤ d := (natDegree_sub_le _ _).trans (max_le hRdeg (by simp))
  refine ⟨c, fun j hj => ?_⟩
  have h := coeff_le_of_separated_evaluations (r := (r : ℝ)) hQdeg hj hN (by exact_mod_cast hr) hε
    (fun i => (v i : ℝ)) (fun i => hSN _ (Finset.mem_filter.mp (hv i)).1)
    (fun i j hij => by exact_mod_cast hsep i j hij)
    (fun i => by
      obtain ⟨hi, he⟩ := Finset.mem_filter.mp (hv i)
      simpa only [Q, eval_sub, eval_C, he] using hLabel (v i) hi)
  have he : Q.coeff j = p.coeff j - (((q + C c).coeff j : ℤ) : ℝ) := by
    simp only [Q, R, coeff_sub, coeff_map, Int.coe_castRingHom, coeff_add, Int.cast_add, sub_sub]
    simp only [coeff_C, Int.cast_ite, Int.cast_zero]
  rwa [he] at h


/-- On a dense set of near-integer values of a monomial phase, a coarse
leading-coefficient approximation at scale `N^(-k)` improves to an
error linear in the near-integer tolerance, with the same denominator. -/
theorem sharpen_monomial_dilation_approximation {k r B q : ℕ} {N ε A α b : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hr : 0 < r) (hN : 0 < N)
    (hε : 0 ≤ ε) (hεq : (q : ℝ) * ε ≤ 1) (a : ℤ)
    (hcoarse : |(q : ℝ) * α - a| ≤ A / N ^ k) (hB : A + 1 ≤ (B : ℝ))
    (S : Finset ℤ) (hcount : (2 * B + 3) * (k * r + 1) ≤ S.card)
    (hSN : ∀ n ∈ S, (n : ℝ) ∈ Set.Icc 0 N)
    (hnear : ∀ n ∈ S, ∃ z : ℤ, |α * (n : ℝ) ^ k + b - z| ≤ ε) :
    |(q : ℝ) * α - a| ≤
      interpolationCoefficientConstant k * ((k + 1 : ℕ) * (N / (r : ℝ)) ^ k * ((q : ℝ) * ε)) /
        N ^ k := by
  let c : ℤ := ⌊(q : ℝ) * b⌋
  let p : ℝ[X] := monomial k ((q : ℝ) * α) + C ((q : ℝ) * b)
  let P : ℤ[X] := monomial k a + C c
  have hp : p.natDegree ≤ k :=
    (natDegree_add_le _ _).trans (max_le (natDegree_monomial_le _) ((natDegree_C _).le.trans (Nat.zero_le _)))
  have hP : P.natDegree ≤ k :=
    (natDegree_add_le _ _).trans (max_le (natDegree_monomial_le _) ((natDegree_C _).le.trans (Nat.zero_le _)))
  have hconst : |(q : ℝ) * b - c| ≤ 1 := by
    have h0 : (c : ℝ) ≤ (q : ℝ) * b := Int.floor_le _
    have h1 : (q : ℝ) * b < (c : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_of_nonneg (sub_nonneg.mpr h0)]
    linarith
  have hA : 0 ≤ A := (mul_nonneg (abs_nonneg _) (pow_nonneg hN.le k)).trans
    ((le_div_iff₀ (pow_pos hN k)).mp hcoarse)
  have hresidual (n : ℤ) (hn : n ∈ S) : |p.eval (n : ℝ) - ((P.eval n : ℤ) : ℝ)| ≤ B := by
    have hx := hSN n hn
    have hpow : (n : ℝ) ^ k ≤ N ^ k := pow_le_pow_left₀ hx.1 hx.2 k
    have heval : p.eval (n : ℝ) - ((P.eval n : ℤ) : ℝ) =
        ((q : ℝ) * α - a) * (n : ℝ) ^ k + ((q : ℝ) * b - c) := by
      simp only [p, P, eval_add, eval_monomial, eval_C, Int.cast_add, Int.cast_mul, Int.cast_pow]
      ring
    rw [heval]
    calc
      _ ≤ |(q : ℝ) * α - a| * (n : ℝ) ^ k + |(q : ℝ) * b - c| := by
        simpa only [abs_mul, abs_of_nonneg (pow_nonneg hx.1 k)] using
          (abs_add_le (((q : ℝ) * α - a) * (n : ℝ) ^ k) ((q : ℝ) * b - c))
      _ ≤ (A / N ^ k) * N ^ k + 1 := add_le_add
        (mul_le_mul hcoarse hpow (pow_nonneg hx.1 k) (div_nonneg hA (pow_nonneg hN.le _))) hconst
      _ = A + 1 := by rw [div_mul_cancel₀ A (pow_ne_zero _ hN.ne')]
      _ ≤ _ := hB
  have hnear' (n : ℤ) (hn : n ∈ S) : ∃ z : ℤ, |p.eval (n : ℝ) - z| ≤ (q : ℝ) * ε := by
    obtain ⟨z, hz⟩ := hnear n hn
    refine ⟨(q : ℤ) * z, ?_⟩
    have he : p.eval (n : ℝ) - (((q : ℤ) * z : ℤ) : ℝ) =
        (q : ℝ) * (α * (n : ℝ) ^ k + b - z) := by
      simp only [p, eval_add, eval_monomial, eval_C, Int.cast_mul, Int.cast_natCast]
      ring
    rw [he, abs_mul, abs_of_nonneg (Nat.cast_pos.mpr hq).le]
    exact mul_le_mul_of_nonneg_left hz (Nat.cast_pos.mpr hq).le
  obtain ⟨z, hz⟩ := refine_integral_polynomial_approximation hN hr (by positivity)
    hεq S hcount hSN p P hp hP hresidual hnear'
  simpa only [p, P, coeff_add, coeff_monomial, coeff_C, if_pos rfl, if_neg hk.ne', add_zero, true_and, if_true] using
    (hz k le_rfl)

end PrimeUniformity
