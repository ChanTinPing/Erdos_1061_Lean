module

public import PrimeUniformity.CubeProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

/-- A multiplicative difference with a distinct weight on each of its two faces. -/
def crossDifference {A : Type*} [Add A] (h : A) (f g : A → ℂ) (x : A) : ℂ :=
  f x * conj (g (x + h))

private theorem cubeProduct_crossDifference {A : Type*} [AddCommSemigroup A]
    (d : ℕ) (f g : A → ℂ) (x a : A) (h : Fin d → A) :
    cubeProduct d (crossDifference a f g) x h =
      cubeProduct d f x h * conj (cubeProduct d g (x + a) h) := by
  change cubeProduct d (fun z => f z * conj (g (z + a))) x h = _
  rw [cubeProduct_mul, cubeProduct_conj, cubeProduct_translate]

private theorem meanR_add' {A : Type*} [Fintype A] (f g : A → ℝ) :
    meanR (fun x => f x + g x) = meanR f + meanR g := by
  simp only [meanR, Finset.sum_add_distrib, add_div]

private theorem meanR_scale {A : Type*} [Fintype A] (r : ℝ) (f : A → ℝ) :
    meanR (fun x => r * f x) = r * meanR f := by
  simp only [meanR, ← Finset.mul_sum, mul_div_assoc]

private theorem meanR_mono' {A : Type*} [Fintype A] (f g : A → ℝ) (h : ∀ a, f a ≤ g a) :
    meanR f ≤ meanR g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

private theorem meanC_add' {A : Type*} [Fintype A] (f g : A → ℂ) :
    meanC (fun x => f x + g x) = meanC f + meanC g := by
  simp only [meanC, Finset.sum_add_distrib, add_div]

/-- Averaging the moment of a mixed difference over all translations factors
the two base-point averages, while retaining the same remaining directions. -/
theorem mean_gowersCubeMoment_crossDifference {K : Type*} [AddCommGroup K] [Fintype K]
    (d : ℕ) (f g : K → ℂ) :
    meanR (fun a => gowersCubeMoment d (crossDifference a f g)) =
      meanR (fun h : Fin d → K =>
        (meanC (fun x => cubeProduct d f x h) *
          conj (meanC (fun y => cubeProduct d g y h))).re) := by
  classical
  let F (h : Fin d → K) (x : K) := cubeProduct d f x h
  let G (h : Fin d → K) (y : K) := cubeProduct d g y h
  let N : ℝ := Fintype.card K
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card K)
  have hcard : (Fintype.card (Fin d → K) : ℝ) = N ^ d := by
    simp [N]
  have hterm (h : Fin d → K) :
      (meanC (F h) * conj (meanC (G h))).re =
        (∑ x : K, ∑ y : K, (F h x * conj (G h y)).re) / N ^ 2 := by
    unfold meanC
    rw [map_div₀, ← Complex.ofReal_natCast]
    simp only [Complex.conj_ofReal, div_mul_div_comm, ← pow_two, ← Complex.ofReal_pow,
      Complex.div_ofReal_re, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    congr 1
    exact Finset.sum_comm
  simp only [gowersCubeMoment_eq_sum, cubeProduct_crossDifference, meanR]
  change ((∑ a : K, (∑ x : K, ∑ h : Fin d → K, (F h x * conj (G h (x + a))).re) /
      N ^ (d + 1)) / N) = (∑ h, (meanC (F h) * conj (meanC (G h))).re) / _
  rw [hcard]
  simp_rw [hterm, div_eq_mul_inv, ← Finset.sum_mul]
  let T (h : Fin d → K) (x a : K) := (F h x * conj (G h (x + a))).re
  have hsum : (∑ a : K, ∑ x : K, ∑ h : Fin d → K, T h x a) =
      ∑ h : Fin d → K, ∑ x : K, ∑ y : K, (F h x * conj (G h y)).re := by
    calc
      _ = ∑ a : K, ∑ h : Fin d → K, ∑ x : K, T h x a := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ h : Fin d → K, ∑ a : K, ∑ x : K, T h x a := Finset.sum_comm
      _ = ∑ h : Fin d → K, ∑ x : K, ∑ a : K, T h x a := by
        apply Finset.sum_congr rfl
        intro h _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact Equiv.sum_comp (Equiv.addLeft x) (fun y => (F h x * conj (G h y)).re)
  change ((∑ a : K, ∑ x : K, ∑ h : Fin d → K, T h x a) * (N ^ (d + 1))⁻¹) * N⁻¹ = _
  rw [hsum, pow_succ, pow_two]
  field_simp [hN.ne'] <;> ring

/-- Positive-order cube moments are averages of squares. -/
theorem gowersCubeMoment_succ_eq_mean_norm_sq {K : Type*} [AddCommGroup K] [Fintype K]
    (d : ℕ) (f : K → ℂ) :
    gowersCubeMoment d.succ f =
      meanR (fun h : Fin d → K => ‖meanC (fun x => cubeProduct d f x h)‖ ^ 2) := by
  change meanR (fun a => gowersCubeMoment d (crossDifference a f f)) = _
  rw [mean_gowersCubeMoment_crossDifference]
  congr 1
  funext h
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem gowersCubeMoment_succ_nonneg {K : Type*} [AddCommGroup K] [Fintype K]
    (d : ℕ) (f : K → ℂ) : 0 ≤ gowersCubeMoment d.succ f := by
  rw [gowersCubeMoment_succ_eq_mean_norm_sq, meanR]
  exact div_nonneg (Finset.sum_nonneg (fun h _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- The averaged mixed-difference moment is bounded by the arithmetic mean
of the two diagonal moments. -/
theorem mean_gowersCubeMoment_crossDifference_le {K : Type*} [AddCommGroup K] [Fintype K]
    (d : ℕ) (f g : K → ℂ) :
    meanR (fun a => gowersCubeMoment d (crossDifference a f g)) ≤
      (gowersCubeMoment d.succ f + gowersCubeMoment d.succ g) / 2 := by
  rw [mean_gowersCubeMoment_crossDifference, gowersCubeMoment_succ_eq_mean_norm_sq,
    gowersCubeMoment_succ_eq_mean_norm_sq]
  simp only [div_eq_mul_inv, mul_comm _ ((2 : ℝ)⁻¹), ← meanR_add', ← meanR_scale]
  apply meanR_mono'
  intro h
  let a := meanC (fun x => cubeProduct d f x h)
  let b := meanC (fun x => cubeProduct d g x h)
  change (a * conj b).re ≤ 2⁻¹ * (‖a‖ ^ 2 + ‖b‖ ^ 2)
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- At every positive order the cube moment of a sum is bounded by a
dimension-dependent multiple of the sum of the two moments. -/
theorem exists_gowersCubeMoment_succ_add_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Type} [AddCommGroup K] [Fintype K] (f g : K → ℂ),
      gowersCubeMoment d.succ (fun x => f x + g x) ≤
        C * (gowersCubeMoment d.succ f + gowersCubeMoment d.succ g) := by
  induction d with
  | zero =>
    refine ⟨2, by norm_num, ?_⟩
    intro K _ _ f g
    simp only [gowersCubeMoment_succ_eq_mean_norm_sq, cubeProduct, meanC_add']
    simp [meanR]
    calc
      _ ≤ (‖meanC f‖ + ‖meanC g‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
      _ ≤ _ := by nlinarith [sq_nonneg (‖meanC f‖ - ‖meanC g‖)]
  | succ d ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨2 * C ^ 2, by positivity, ?_⟩
    intro K _ _ f g
    let M := fun k : K → ℂ => gowersCubeMoment d.succ k
    let H := fun a (s t : K → ℂ) => crossDifference a s t
    have hsplit (a : K) :
        difference a (fun x => f x + g x) =
          fun x => (H a f f x + H a f g x) + (H a g f x + H a g g x) := by
      funext x
      simp only [difference, H, crossDifference, map_add, add_mul, mul_add]
      ac_rfl
    have hbound (a : K) :
        M (difference a (fun x => f x + g x)) ≤
          C ^ 2 * ((M (H a f f) + M (H a f g)) + (M (H a g f) + M (H a g g))) := by
      rw [hsplit]
      refine (ih _ _).trans ?_
      calc
        _ ≤ C * (C * (M (H a f f) + M (H a f g)) + C * (M (H a g f) + M (H a g g))) :=
          mul_le_mul_of_nonneg_left (add_le_add (ih _ _) (ih _ _)) hC.le
        _ = _ := by ring
    change meanR (fun a => M (difference a (fun x => f x + g x))) ≤ _
    refine (meanR_mono' _ _ hbound).trans ?_
    rw [meanR_scale]
    simp only [meanR_add']
    change C ^ 2 * ((gowersCubeMoment d.succ.succ f + meanR (fun a => M (H a f g))) +
        (meanR (fun a => M (H a g f)) + gowersCubeMoment d.succ.succ g)) ≤ _
    refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right
      (mean_gowersCubeMoment_crossDifference_le d.succ f g) _)
      (add_le_add_left (mean_gowersCubeMoment_crossDifference_le d.succ g f) _))
      (sq_nonneg C) |>.trans_eq ?_
    ring

end PrimeUniformity
