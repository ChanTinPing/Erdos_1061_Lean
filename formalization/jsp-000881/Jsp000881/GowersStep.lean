module

public import PrimeUniformity.Gowers
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section

namespace Jsp000881

export PrimeUniformity (meanR meanC difference)

open scoped BigOperators ComplexConjugate

/-- Cauchy–Schwarz in the first coordinate after averaging in the second. -/
theorem norm_sq_sum_factor_le {U V : Type*} [Fintype U] [Fintype V]
    (g : U → ℂ) (f : U → V → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1) :
    ‖∑ u, ∑ v, g u * f u v‖ ^ 2 ≤
      (Fintype.card U : ℝ) * ∑ u, ‖∑ v, f u v‖ ^ 2 := by
  have h : ‖∑ u, ∑ v, g u * f u v‖ ≤ ∑ u, ‖∑ v, f u v‖ := by
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ u, ‖g u * (∑ v, f u v)‖ := norm_sum_le Finset.univ _
      _ ≤ _ := Finset.sum_le_sum fun u _ => by
        rw [norm_mul]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hg u) (norm_nonneg (∑ v, f u v))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun u => ‖∑ v, f u v‖))

/-- The square of a sum is the sum of all additive correlations. -/
theorem norm_sq_sum_eq_translated_pairs {V : Type*} [AddGroup V] [Fintype V] (f : V → ℂ) :
    ‖∑ v, f v‖ ^ 2 = ∑ v, ∑ h, (f v * conj (f (v + h))).re := by
  calc
    _ = ((∑ v, f v) * conj (∑ v, f v)).re := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    _ = ∑ v, ∑ w, (f v * conj (f w)).re := by
      simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Equiv.sum_comp (Equiv.addLeft v) fun w => (f v * conj (f w)).re).symm

def linearRow {K : Type*} [Field K] (a b : K) (x : K × K) : K :=
  a * x.1 + b * x.2

/-- A nonzero row is the first coordinate of an invertible linear change. -/
noncomputable def rowCoordinates {K : Type*} [Field K] (a b : K)
    (h : a ≠ 0 ∨ b ≠ 0) : (K × K) ≃ (K × K) := by
  classical
  exact if ha : a ≠ 0 then
    { toFun := fun x => (linearRow a b x, x.2)
      invFun := fun y => ((y.1 - b * y.2) / a, y.2)
      left_inv := fun x => by
        apply Prod.ext
        · dsimp [linearRow]
          field_simp [ha] <;> ring
        · rfl
      right_inv := fun y => by
        apply Prod.ext
        · dsimp [linearRow]
          field_simp [ha] <;> ring
        · rfl }
  else
    let hb := h.resolve_left ha
    { toFun := fun x => (linearRow a b x, x.1)
      invFun := fun y => (y.2, (y.1 - a * y.2) / b)
      left_inv := fun x => by
        apply Prod.ext
        · rfl
        · dsimp [linearRow]
          field_simp [hb] <;> ring
      right_inv := fun y => by
        apply Prod.ext
        · dsimp [linearRow]
          field_simp [hb] <;> ring
        · rfl }

theorem rowCoordinates_fst {K : Type*} [Field K] (a b : K) (h : a ≠ 0 ∨ b ≠ 0) (x : K × K) :
    (rowCoordinates a b h x).1 = linearRow a b x := by
  classical
  unfold rowCoordinates
  split <;> rfl

theorem rowCoordinates_kernel_translation {K : Type*} [Field K] (a b : K)
    (h : a ≠ 0 ∨ b ≠ 0) (u v w : K) :
    (rowCoordinates a b h).symm (u, v + w) =
      (rowCoordinates a b h).symm (u, v) + (rowCoordinates a b h).symm (0, w) := by
  classical
  unfold rowCoordinates
  split <;> apply Prod.ext <;> simp [div_eq_mul_inv] <;> ring

/-- Eliminate one bounded affine weight by differencing along its row's kernel. -/
theorem directional_cauchy_schwarz {K : Type*} [Field K] [Fintype K]
    (a b c : K) (h : a ≠ 0 ∨ b ≠ 0) (g : K → ℂ) (f : K × K → ℂ)
    (hg : ∀ t, ‖g t‖ ≤ 1) :
    ‖∑ x, g (linearRow a b x + c) * f x‖ ^ 2 ≤
      (Fintype.card K : ℝ) * ∑ x, ∑ w,
        (f x * conj (f (x + (rowCoordinates a b h).symm (0, w)))).re := by
  classical
  let e := rowCoordinates a b h
  have hsum : (∑ x, g (linearRow a b x + c) * f x) =
      ∑ u, ∑ v, g (u + c) * f (e.symm (u, v)) := by
    rw [← Fintype.sum_prod_type' (fun u v => g (u + c) * f (e.symm (u, v)))]
    apply Fintype.sum_equiv e
    intro x
    change g (linearRow a b x + c) * f x = g ((e x).1 + c) * f (e.symm (e x))
    rw [e.symm_apply_apply, show (e x).1 = linearRow a b x from rowCoordinates_fst _ _ _ _]
  rw [hsum]
  refine (norm_sq_sum_factor_le (fun u => g (u + c)) (fun u v => f (e.symm (u, v)))
    (fun u => hg (u + c))).trans_eq ?_
  apply congrArg (fun t : ℝ => (Fintype.card K : ℝ) * t)
  simp_rw [norm_sq_sum_eq_translated_pairs]
  have ht (u v w : K) : e.symm (u, v + w) = e.symm (u, v) + e.symm (0, w) :=
    rowCoordinates_kernel_translation a b h u v w
  simp_rw [ht]
  let Q := fun x : K × K => ∑ w : K, (f x * conj (f (x + e.symm (0, w)))).re
  change (∑ u : K, ∑ v : K, Q (e.symm (u, v))) = ∑ x, Q x
  rw [← Fintype.sum_prod_type' (fun u v => Q (e.symm (u, v)))]
  exact Equiv.sum_comp e.symm Q

theorem meanR_pow_succ_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    meanR f ^ (n + 1) ≤ meanR (fun x => f x ^ (n + 1)) := by
  have hc : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset A))
    (fun x _ => hf x) n
  unfold meanR
  rw [div_pow, show (Fintype.card A : ℝ) ^ (n + 1) =
    (Fintype.card A : ℝ) ^ n * (Fintype.card A : ℝ) from pow_succ _ _, ← div_div]
  exact div_le_div_of_nonneg_right (by simpa only [Finset.card_univ] using h) hc.le

theorem directional_cauchy_schwarz_mean {K : Type*} [Field K] [Fintype K]
    (a b c : K) (h : a ≠ 0 ∨ b ≠ 0) (g : K → ℂ) (f : K × K → ℂ)
    (hg : ∀ t, ‖g t‖ ≤ 1) :
    ‖meanC (fun x => g (linearRow a b x + c) * f x)‖ ^ 2 ≤
      meanR fun w => meanR fun x =>
        (f x * conj (f (x + (rowCoordinates a b h).symm (0, w)))).re := by
  let N : ℝ := Fintype.card K
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card K)
  let q : (K × K) → K → ℝ :=
    fun x w => (f x * conj (f (x + (rowCoordinates a b h).symm (0, w)))).re
  have hraw : ‖∑ x, g (linearRow a b x + c) * f x‖ ^ 2 ≤ N * ∑ x, ∑ w, q x w :=
    directional_cauchy_schwarz a b c h g f hg
  unfold meanC
  rw [norm_div, Complex.norm_natCast, div_pow, show (Fintype.card (K × K) : ℝ) = N ^ 2 by
    simp only [Fintype.card_prod, Nat.cast_mul, pow_two, N]]
  refine (div_le_div_of_nonneg_right hraw (by positivity)).trans_eq ?_
  change N * (∑ x, ∑ w, q x w) / (N ^ 2) ^ 2 = meanR (fun w => meanR fun x => q x w)
  unfold meanR
  simp only [Fintype.card_prod, Nat.cast_mul]
  change N * (∑ x, ∑ w, q x w) / (N ^ 2) ^ 2 =
    (∑ w, (∑ x, q x w) / (N * N)) / N
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  field_simp [hN.ne'] <;> ring

theorem difference_norm_le_one {A : Type*} [Add A] (h : A) (f : A → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (x : A) : ‖difference h f x‖ ≤ 1 := by
  unfold difference
  rw [norm_mul, Complex.norm_conj]
  simpa only [mul_one] using
    mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem difference_product {A ι : Type*} [Add A] (h : A) (F : Finset ι)
    (f : ι → A → ℂ) (x : A) :
    difference h (fun y => ∏ i ∈ F, f i y) x = ∏ i ∈ F, difference h (f i) x := by
  simp only [difference, map_prod, Finset.prod_mul_distrib]

theorem meanC_re_eq_meanR {A : Type*} [Fintype A] (f : A → ℂ) :
    (meanC f).re = meanR (fun x => (f x).re) := by
  unfold meanC meanR
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]

theorem meanR_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ x, f x ≤ g x) :
    meanR f ≤ meanR g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

theorem meanR_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ meanR f :=
  div_nonneg (Finset.sum_nonneg fun x _ => h x) (Nat.cast_nonneg _)

private theorem mul_left_bijection {K : Type*} [Field K] (k : K) (hk : k ≠ 0) :
    Function.Bijective (fun v : K => k * v) := by
  refine ⟨fun _ _ h => mul_left_cancel₀ hk h, fun y => ⟨y / k, ?_⟩⟩
  change k * (y / k) = y
  rw [mul_comm, div_mul_cancel₀ _ hk]

/-- An independent row maps the kernel of a nonzero row bijectively onto
the one-dimensional field. This is the uniformity of the final increments. -/
theorem independent_row_on_kernel_bijective {K : Type*} [Field K]
    (a b c d : K) (h : a ≠ 0 ∨ b ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Function.Bijective (fun w => linearRow c d ((rowCoordinates a b h).symm (0, w))) := by
  classical
  unfold rowCoordinates
  split
  · rename_i ha
    let k := d - c * b / a
    have hk : k ≠ 0 := by
      intro hz
      apply hdet
      calc
        _ = a * k := by dsimp [k]; field_simp [ha] <;> ring
        _ = 0 := by rw [hz, mul_zero]
    have hfun : (fun w : K => linearRow c d (((0 - b * w) / a), w)) = fun w => k * w := by
      funext w
      simp only [linearRow, k, div_eq_mul_inv]
      ring
    change Function.Bijective (fun w : K => linearRow c d (((0 - b * w) / a), w))
    rw [hfun]
    exact mul_left_bijection k hk
  · rename_i ha
    have hb := h.resolve_left ha
    let k := c - d * a / b
    have hk : k ≠ 0 := by
      intro hz
      apply hdet
      calc
        _ = -(b * k) := by dsimp [k]; field_simp [hb] <;> ring
        _ = 0 := by rw [hz, mul_zero, neg_zero]
    have hfun : (fun w : K => linearRow c d (w, (0 - a * w) / b)) = fun w => k * w := by
      funext w
      simp only [linearRow, k, div_eq_mul_inv]
      ring
    change Function.Bijective (fun w : K => linearRow c d (w, (0 - a * w) / b))
    rw [hfun]
    exact mul_left_bijection k hk

theorem difference_linearRow {K : Type*} [Field K] (a b c : K)
    (h x : K × K) (f : K → ℂ) :
    difference h (fun y => f (linearRow a b y + c)) x =
      difference (linearRow a b h) f (linearRow a b x + c) := by
  unfold difference
  have he : linearRow a b (x + h) + c = (linearRow a b x + c) + linearRow a b h := by
    simp only [linearRow, Prod.fst_add, Prod.snd_add]
    ring
  simpa only [he]

/-- One Cauchy–Schwarz step, with Jensen allowing subsequent steps to be
applied separately to each new difference parameter. -/
theorem directional_cauchy_schwarz_power {K : Type*} [Field K] [Fintype K]
    (a b c : K) (h : a ≠ 0 ∨ b ≠ 0) (g : K → ℂ) (f : K × K → ℂ)
    (hg : ∀ t, ‖g t‖ ≤ 1) (m : ℕ) :
    ‖meanC (fun x => g (linearRow a b x + c) * f x)‖ ^ (2 * (m + 1)) ≤
      meanR fun w => ‖meanC (difference ((rowCoordinates a b h).symm (0, w)) f)‖ ^ (m + 1) := by
  let D := fun w : K => meanC (difference ((rowCoordinates a b h).symm (0, w)) f)
  let V := meanC (fun x => g (linearRow a b x + c) * f x)
  have h₀ : ‖V‖ ^ 2 ≤ meanR (fun w => (D w).re) := by
    simp only [D, meanC_re_eq_meanR, difference]
    exact directional_cauchy_schwarz_mean a b c h g f hg
  have h₁ := h₀.trans (meanR_mono fun w => Complex.re_le_norm (D w))
  change ‖V‖ ^ (2 * (m + 1)) ≤ meanR fun w => ‖D w‖ ^ (m + 1)
  calc
    _ = (‖V‖ ^ 2) ^ (m + 1) := pow_mul _ _ _
    _ ≤ (meanR fun w => ‖D w‖) ^ (m + 1) :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ _
    _ ≤ _ := meanR_pow_succ_le _ (fun w => norm_nonneg (D w)) m

end Jsp000881
