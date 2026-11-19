module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- Reconstruct one graded horizontal coefficient from the estimates on its
annihilator rows. If the integer matrix `A` lifts the row coordinates
with denominator `r`, the rational correction has denominator `q*r`.
The smooth correction keeps the error scale of the row estimates. -/
theorem exists_horizontal_coefficient_split
    {ι κ : Type*} [Fintype κ]
    (η : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (R : (κ → ℝ) →ₗ[ℝ] (ι → ℝ))
    (A : ι → κ → ℤ) (hR : ∀ y i, R y i = ∑ j, (A i j : ℝ) * y j)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hηR : ∀ y, η (R y) = (r : ℝ) • y)
    (x : ι → ℝ) (a : κ → ℤ) {E M : ℝ}
    (hA : ∀ i j, |(A i j : ℝ)| ≤ M)
    (herror : ∀ j, |(q : ℝ) * η x j - (a j : ℝ)| ≤ E) :
    ∃ y ε : ι → ℝ, ∃ z : ι → ℤ,
      η y = 0 ∧
      (∀ i, x i = y i + ε i + (z i : ℝ) / ((q : ℝ) * r)) ∧
      ∀ i, |ε i| ≤ (Fintype.card κ : ℝ) * M * E / ((q : ℝ) * r) := by
  let u : κ → ℝ := fun j => (a j : ℝ)
  let v : κ → ℝ := (q : ℝ) • η x - u
  let y := x - (r : ℝ)⁻¹ • R (η x)
  let ε := ((q : ℝ) * r)⁻¹ • R v
  let z : ι → ℤ := fun i => ∑ j, A i j * a j
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hr' : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  refine ⟨y, ε, z, ?_, ?_, ?_⟩
  · change η (x - (r : ℝ)⁻¹ • R (η x)) = 0
    rw [map_sub, map_smul, hηR, smul_smul, inv_mul_cancel₀ hr'.ne', one_smul, sub_self]
  · intro i
    have hcast : (z i : ℝ) = R u i := by
      simp only [z, hR, Int.cast_sum, Int.cast_mul, u]
    have hdecomp : R v i = (q : ℝ) * R (η x) i - R u i := by
      change R ((q : ℝ) • η x - u) i = _
      rw [map_sub, map_smul]
      rfl
    simp only [y, ε, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcast, hdecomp]
    field_simp
    ring
  · intro i
    change |((q : ℝ) * r)⁻¹ * R v i| ≤ _
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hq'.le hr'.le)), hR]
    have hv (j : κ) : |v j| ≤ E := herror j
    calc
      _ ≤ ((q : ℝ) * r)⁻¹ * ∑ j, |(A i j : ℝ) * v j| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (inv_nonneg.mpr (mul_nonneg hq'.le hr'.le))
      _ ≤ ((q : ℝ) * r)⁻¹ * ∑ _j : κ, M * E := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_nonneg hq'.le hr'.le))
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hA i j) (hv j) (abs_nonneg _) ((abs_nonneg _).trans (hA i j))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]; ring

/-- Evaluate the positive-degree part of an ordinary polynomial with (K)
coefficients. The coefficient at index `j` is that of degree `j+1`. -/
noncomputable def positiveDegreeEval {K : ℕ} (a : Fin K → ℝ) (t : ℝ) : ℝ :=
  ∑ j, a j * t ^ (j.val + 1)

/-- A coefficient bound of order `N^(-j-1)` controls the polynomial uniformly
on the interval of radius `N`. -/
theorem abs_positiveDegreeEval_le {K : ℕ} (a : Fin K → ℝ) {N S t : ℝ}
    (hN : 0 < N) (hS : 0 ≤ S) (ht : |t| ≤ N)
    (ha : ∀ j, |a j| ≤ S / N ^ (j.val + 1)) :
    |positiveDegreeEval a t| ≤ (K : ℝ) * S := by
  calc
    _ ≤ ∑ j : Fin K, |a j * t ^ (j.val + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin K, S := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_pow]
      calc
        _ ≤ (S / N ^ (j.val + 1)) * N ^ (j.val + 1) := by
          gcongr
          exact ha j
        _ = S := div_mul_cancel₀ _ (pow_ne_zero _ hN.ne')
    _ = _ := by simp [nsmul_eq_mul]

/-- On the same interval the positive-degree correction is Lipschitz with an
explicit bound proportional to `1/N`. -/
theorem abs_positiveDegreeEval_sub_le {K : ℕ} (a : Fin K → ℝ) {N S t u : ℝ}
    (hN : 0 < N) (hS : 0 ≤ S) (ht : |t| ≤ N) (hu : |u| ≤ N)
    (ha : ∀ j, |a j| ≤ S / N ^ (j.val + 1)) :
    |positiveDegreeEval a t - positiveDegreeEval a u| ≤
      (K : ℝ) ^ 2 * S / N * |t - u| := by
  simp only [positiveDegreeEval, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ j : Fin K, |a j * (t ^ (j.val + 1) - u ^ (j.val + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin K, (K : ℝ) * S / N * |t - u| := by
      apply Finset.sum_le_sum
      intro j _
      have hpow : |t ^ (j.val + 1) - u ^ (j.val + 1)| ≤ |t - u| * (K : ℝ) * N ^ j.val := by
        apply (abs_pow_sub_pow_le (a := t) (b := u) (n := j.val + 1)).trans
        rw [Nat.add_sub_cancel]
        gcongr
        · exact_mod_cast j.isLt
        · exact max_le ht hu
      rw [abs_mul]
      calc
        _ ≤ (S / N ^ (j.val + 1)) * (|t - u| * (K : ℝ) * N ^ j.val) := by
          gcongr
          exact ha j
        _ = _ := by rw [pow_succ]; field_simp
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Evaluating a polynomial with coefficients of common denominator `D` on
congruent integer inputs gives the same value modulo the integers. -/
theorem rational_positiveDegreeEval_sub_eq_int {K D : ℕ} (a : Fin K → ℤ) (hD : 0 < D)
    {t u : ℤ} (hmod : (D : ℤ).ModEq u t) :
    ∃ z : ℤ, positiveDegreeEval (fun j => (a j : ℝ) / (D : ℝ)) (t : ℝ) -
        positiveDegreeEval (fun j => (a j : ℝ) / (D : ℝ)) (u : ℝ) = z := by
  have hdiv : (D : ℤ) ∣ ∑ j, (a j * t ^ (j.val + 1) - a j * u ^ (j.val + 1)) := by
    apply Finset.dvd_sum
    intro j _
    exact Int.modEq_iff_dvd.mp ((hmod.pow (j.val + 1)).mul_left (a j))
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z, ?_⟩
  have hzR : (∑ j, ((a j : ℝ) * (t : ℝ) ^ (j.val + 1) -
      (a j : ℝ) * (u : ℝ) ^ (j.val + 1))) = (D : ℝ) * (z : ℝ) := by
    exact_mod_cast hz
  rw [positiveDegreeEval, positiveDegreeEval, ← Finset.sum_sub_distrib]
  calc
    _ = (∑ j, ((a j : ℝ) * (t : ℝ) ^ (j.val + 1) -
        (a j : ℝ) * (u : ℝ) ^ (j.val + 1))) / D := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = z := by rw [hzR, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hD.ne')]

/-- Split each positive-degree horizontal coefficient using the corresponding
row map. One denominator works for all rational coordinates, and the smooth
correction satisfies uniform value and increment bounds on the original scale. -/
theorem exists_horizontal_positive_degree_split
    {K : ℕ} {ι : Type*} {κ : Fin K → Type*} [∀ j, Fintype (κ j)]
    (η : ∀ j, (ι → ℝ) →ₗ[ℝ] (κ j → ℝ)) (R : ∀ j, (κ j → ℝ) →ₗ[ℝ] (ι → ℝ))
    (A : ∀ j, ι → κ j → ℤ) (hR : ∀ j y i, R j y i = ∑ l, (A j i l : ℝ) * y l)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hηR : ∀ j y, η j (R j y) = (r : ℝ) • y)
    (x : Fin K → ι → ℝ) (a : ∀ j, κ j → ℤ) {N H M V : ℝ}
    (hN : 0 < N) (hH : 0 ≤ H) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hcard : ∀ j, (Fintype.card (κ j) : ℝ) ≤ V)
    (hA : ∀ j i l, |(A j i l : ℝ)| ≤ M)
    (herror : ∀ j l, |(q : ℝ) * η j (x j) l - (a j l : ℝ)| ≤ H / N ^ (j.val + 1)) :
    let S := V * M * H / ((q : ℝ) * r)
    ∃ y ε : Fin K → ι → ℝ, ∃ z : Fin K → ι → ℤ,
      (∀ j, η j (y j) = 0) ∧
      (∀ j i, x j i = y j i + ε j i + (z j i : ℝ) / ((q : ℝ) * r)) ∧
      (∀ i t, positiveDegreeEval (fun j => x j i) t =
        positiveDegreeEval (fun j => y j i) t + positiveDegreeEval (fun j => ε j i) t +
          positiveDegreeEval (fun j => (z j i : ℝ) / ((q : ℝ) * r)) t) ∧
      (∀ j i, |ε j i| ≤ S / N ^ (j.val + 1)) ∧
      (∀ i t, |t| ≤ N → |positiveDegreeEval (fun j => ε j i) t| ≤ (K : ℝ) * S) ∧
      (∀ i t u, |t| ≤ N → |u| ≤ N →
        |positiveDegreeEval (fun j => ε j i) t - positiveDegreeEval (fun j => ε j i) u| ≤
          (K : ℝ) ^ 2 * S / N * |t - u|) ∧
      (∀ i (t u : ℤ), (↑(q * r) : ℤ).ModEq u t → ∃ b : ℤ,
        positiveDegreeEval (fun j => (z j i : ℝ) / ((q : ℝ) * r)) (t : ℝ) -
          positiveDegreeEval (fun j => (z j i : ℝ) / ((q : ℝ) * r)) (u : ℝ) = b) := by
  intro S
  obtain h := fun j => exists_horizontal_coefficient_split (η j) (R j) (A j) (hR j) q r hq hr
    (hηR j) (x j) (a j) (hA j) (herror j)
  choose y ε z hy hx hε using h
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hε' (j : Fin K) (i : ι) : |ε j i| ≤ S / N ^ (j.val + 1) := by
    apply (hε j i).trans
    calc
      _ ≤ V * M * (H / N ^ (j.val + 1)) / ((q : ℝ) * r) := by
        gcongr
        exact hcard j
      _ = _ := by simp only [S]; ring
  refine ⟨y, ε, z, hy, hx, ?_, hε', ?_, ?_, ?_⟩
  · intro i t
    simp only [positiveDegreeEval, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hx j i]
    ring
  · intro i t ht
    exact abs_positiveDegreeEval_le _ hN hS ht (fun j => hε' j i)
  · intro i t u ht hu
    exact abs_positiveDegreeEval_sub_le _ hN hS ht hu (fun j => hε' j i)
  · intro i t u hmod
    simpa only [Nat.cast_mul] using
      rational_positiveDegreeEval_sub_eq_int (fun j => z j i) (Nat.mul_pos hq hr) hmod

end PrimeUniformity
