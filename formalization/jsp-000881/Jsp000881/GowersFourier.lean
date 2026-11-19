module

public import Jsp000881.GowersIteration
import all Jsp000881.GowersIteration

public section

namespace Jsp000881

open scoped BigOperators

private def twistWeight {K : Type*} [Field K] (χ : K → ℂ) (hχ : ∀ t, ‖χ t‖ = 1)
    (r : K) (g : BoundedAffineWeight K) : BoundedAffineWeight K :=
  { dir := g.dir
    c := g.c
    weight := fun t => χ (r * (t - g.c)) * g.weight t
    norm_le_one := fun t => by
      rw [norm_mul, hχ, one_mul]
      exact g.norm_le_one t }

private theorem twisted_correlation_bound {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hχ : ∀ t, ‖χ t‖ = 1) (hadd : ∀ u v, χ (u + v) = χ u * χ v)
    (g₁ g₂ : BoundedAffineWeight K) (gs : List (BoundedAffineWeight K)) (hlen : gs.length = 3)
    (hdet : g₁.dir.a * g₂.dir.b - g₁.dir.b * g₂.dir.a ≠ 0)
    (d : LinearDirection K) (c : K) (f : K → ℂ)
    (h : ∀ g ∈ g₁ :: g₂ :: gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0)
    {G : ℝ} (hG : 0 ≤ G) (hf : gowersCubeMoment 5 f ≤ G ^ 32) (u v : K) :
    ‖meanC (fun x : K × K => χ (u * x.1 + v * x.2) *
      (f (linearRow d.a d.b x + c) * affineWeightProduct x (g₁ :: g₂ :: gs)))‖ ≤ G := by
  let Δ := g₁.dir.a * g₂.dir.b - g₁.dir.b * g₂.dir.a
  let r := (u * g₂.dir.b - v * g₂.dir.a) / Δ
  let s := (g₁.dir.a * v - g₁.dir.b * u) / Δ
  have hΔ : Δ ≠ 0 := hdet
  have h₁ : r * g₁.dir.a + s * g₂.dir.a = u := by
    dsimp only [r, s]
    field_simp [hΔ]
    dsimp [Δ]
    ring
  have h₂ : r * g₁.dir.b + s * g₂.dir.b = v := by
    dsimp only [r, s]
    field_simp [hΔ]
    dsimp [Δ]
    ring
  let w₁ := twistWeight χ hχ r g₁
  let w₂ := twistWeight χ hχ s g₂
  have he (x : K × K) : u * x.1 + v * x.2 =
      r * linearRow g₁.dir.a g₁.dir.b x + s * linearRow g₂.dir.a g₂.dir.b x := by
    rw [← h₁, ← h₂]
    unfold linearRow
    ring
  have hsplit (x : K × K) : χ (u * x.1 + v * x.2) *
        (f (linearRow d.a d.b x + c) * affineWeightProduct x (g₁ :: g₂ :: gs)) =
      f (linearRow d.a d.b x + c) * affineWeightProduct x (w₁ :: w₂ :: gs) := by
    rw [he, hadd]
    simp only [affineWeightProduct, BoundedAffineWeight.eval, w₁, w₂, twistWeight,
      add_sub_cancel_right]
    ring
  have hlen' : (w₁ :: w₂ :: gs).length = 4 + 1 := by simp [hlen]
  have h' : ∀ g ∈ w₁ :: w₂ :: gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h g₁ List.mem_cons_self
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h g₂ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact h g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
  simp_rw [hsplit]
  apply le_of_pow_le_pow_left₀ (by decide : (32 : ℕ) ≠ 0) hG
  exact (affine_system_gowers_bound 4 (w₁ :: w₂ :: gs) hlen' d c h' f).trans hf

private theorem meanC_sum {K A : Type*} [Fintype K] [Fintype A] (F : A → K → ℂ) :
    meanC (fun x => ∑ a, F a x) = ∑ a, meanC (F a) := by
  unfold meanC
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]

theorem meanC_mul_left {K : Type*} [Fintype K] (a : ℂ) (F : K → ℂ) :
    meanC (fun x => a * F x) = a * meanC F := by
  unfold meanC
  rw [← Finset.mul_sum, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- Product of the two one-dimensional Fourier ℓ¹ norms is the entire loss
from inserting two coordinate weights into a six-form correlation. -/
theorem coordinate_weights_gowers_bound {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hχ : ∀ t, ‖χ t‖ = 1) (hadd : ∀ u v, χ (u + v) = χ u * χ v)
    (g₁ g₂ : BoundedAffineWeight K) (gs : List (BoundedAffineWeight K)) (hlen : gs.length = 3)
    (hdet : g₁.dir.a * g₂.dir.b - g₁.dir.b * g₂.dir.a ≠ 0)
    (d : LinearDirection K) (c : K) (f A B a b : K → ℂ)
    (h : ∀ g ∈ g₁ :: g₂ :: gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0)
    (hA : ∀ x, A x = ∑ u, a u * χ (u * x))
    (hB : ∀ x, B x = ∑ v, b v * χ (v * x))
    {G : ℝ} (hG : 0 ≤ G) (hf : gowersCubeMoment 5 f ≤ G ^ 32) :
    ‖meanC (fun x : K × K => A x.1 * B x.2 *
      (f (linearRow d.a d.b x + c) * affineWeightProduct x (g₁ :: g₂ :: gs)))‖ ≤
      (∑ u, ‖a u‖) * (∑ v, ‖b v‖) * G := by
  let H := fun x : K × K => f (linearRow d.a d.b x + c) *
    affineWeightProduct x (g₁ :: g₂ :: gs)
  let integrand := fun u v : K => fun x : K × K => χ (u * x.1 + v * x.2) * H x
  have hexpand (x : K × K) : A x.1 * B x.2 * H x =
      ∑ u, ∑ v, (a u * b v) * integrand u v x := by
    rw [hA, hB, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [integrand]
    rw [hadd]
    ring
  have hb (u v : K) : ‖meanC (integrand u v)‖ ≤ G :=
    twisted_correlation_bound χ hχ hadd g₁ g₂ gs hlen hdet d c f h hG hf u v
  change ‖meanC (fun x : K × K => A x.1 * B x.2 * H x)‖ ≤ _
  simp_rw [hexpand, meanC_sum, meanC_mul_left]
  calc
    _ ≤ ∑ u, ‖∑ v, (a u * b v) * meanC (integrand u v)‖ := norm_sum_le _ _
    _ ≤ ∑ u, ∑ v, ‖a u‖ * ‖b v‖ * G := by
      apply Finset.sum_le_sum
      intro u _
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
      intro v _
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb u v) (by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Normalized coefficient of an additive character of the finite field. -/
noncomputable def coordinateFourier {K : Type*} [Field K] [Fintype K]
    (χ A : K → ℂ) (u : K) : ℂ :=
  meanC fun y => A y * χ (-(u * y))

private theorem sum_mul_character {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hadd : ∀ u v, χ (u + v) = χ u * χ v)
    (hnontrivial : ∃ v, χ v ≠ 1) (z : K) :
    (∑ u, χ (u * z)) = if z = 0 then (Fintype.card K : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · simp [hz, hzero]
  · obtain ⟨v, hv⟩ := hnontrivial
    let w := v / z
    have hw : w * z = v := div_mul_cancel₀ _ hz
    let S := ∑ u, χ (u * z)
    have htranslate : (∑ u : K, χ ((w + u) * z)) = S :=
      Equiv.sum_comp (Equiv.addLeft w) (fun u => χ (u * z))
    simp_rw [add_mul, hw, hadd, ← Finset.mul_sum] at htranslate
    change χ v * S = S at htranslate
    have hprod : (χ v - 1) * S = 0 := by rw [sub_mul, one_mul, htranslate, sub_self]
    rw [if_neg hz]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hv)

theorem coordinateFourier_inversion {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hadd : ∀ u v, χ (u + v) = χ u * χ v)
    (hnontrivial : ∃ v, χ v ≠ 1) (A : K → ℂ) (x : K) :
    A x = ∑ u, coordinateFourier χ A u * χ (u * x) := by
  classical
  let N : ℂ := Fintype.card K
  have hN : N ≠ 0 := by
    change (Fintype.card K : ℂ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  symm
  calc
    _ = (∑ u, ∑ y, A y * χ (u * (x - y))) / N := by
      unfold coordinateFourier meanC
      simp only [div_eq_mul_inv]
      conv_rhs => rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_sub, sub_eq_neg_add, hadd]
      ring
    _ = (∑ y, A y * (if x - y = 0 then N else 0)) / N := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_mul_character χ hzero hadd hnontrivial]
      rfl
    _ = A x := by
      simp only [sub_eq_zero, eq_comm (a := x), mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, mul_div_cancel_right₀ _ hN]

end Jsp000881
