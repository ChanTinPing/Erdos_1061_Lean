module

public import Jsp000881.GowersFourier
import all Jsp000881.GowersFourier

public section

namespace Jsp000881

open Classical
open scoped BigOperators ComplexConjugate

/-- The autocorrelation of an indicator, normalized to one at the origin. -/
noncomputable def triangleCutoff {K : Type*} [Add K] (E : Finset K) (t : K) : ℂ := by
  exact ((E.filter fun x => x + t ∈ E).card : ℂ) / (E.card : ℂ)

theorem triangleCutoff_zero {K : Type*} [AddZeroClass K] {E : Finset K}
    (hE : E.Nonempty) : triangleCutoff E 0 = 1 := by
  have hf : E.filter (fun x => x + 0 ∈ E) = E := by
    ext x
    simp
  have hcard : (E.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hE)
  unfold triangleCutoff
  rw [hf, div_self hcard]

private theorem triangleCutoff_eq_sum {K : Type*} [Add K] (E : Finset K) (t : K) :
    triangleCutoff E t = (∑ x ∈ E, if x + t ∈ E then (1 : ℂ) else 0) / (E.card : ℂ) := by
  unfold triangleCutoff
  congr 1
  rw [← Finset.sum_filter]
  simp

private theorem translate_character_sum {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (E : Finset K) (u x : K) :
    (∑ t : K, if x + t ∈ E then χ (-(u * t)) else 0) =
      ∑ y ∈ E, χ (-(u * (y - x))) := by
  calc
    _ = ∑ y : K, if y ∈ E then χ (-(u * (y - x))) else 0 := by
      apply Fintype.sum_equiv (Equiv.addLeft x)
      intro t
      change (if x + t ∈ E then χ (-(u * t)) else 0) =
        (if x + t ∈ E then χ (-(u * (x + t - x))) else 0)
      rw [show x + t - x = t by ring]
    _ = _ := by
      rw [← Finset.sum_filter]
      have hfilter : (Finset.univ : Finset K).filter (fun y => y ∈ E) = E := by
        ext y
        simp
      rw [hfilter]

private theorem character_neg_eq_conj {K : Type*} [AddGroup K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hnorm : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (x : K) : χ (-x) = conj (χ x) := by
  have hx : χ x ≠ 0 := by
    intro h
    have h' := hnorm x
    rw [h, norm_zero] at h'
    exact zero_ne_one h'
  apply mul_left_cancel₀ hx
  rw [← hadd, add_neg_cancel, hzero, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, hnorm]

/-- The Fourier coefficients are squared moduli divided by the two cardinalities. -/
theorem triangleCutoff_fourier {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hnorm : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (E : Finset K) (u : K) :
    coordinateFourier χ (triangleCutoff E) u =
      ((‖∑ x ∈ E, χ (u * x)‖ ^ 2 / (E.card : ℝ) / (Fintype.card K : ℝ) : ℝ) : ℂ) := by
  have hpoint (t : K) : triangleCutoff E t * χ (-(u * t)) =
      (∑ x ∈ E, if x + t ∈ E then χ (-(u * t)) else 0) / (E.card : ℂ) := by
    rw [triangleCutoff_eq_sum, div_mul_eq_mul_div₀, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp [*]
  have hphase (x y : K) : -(u * (y - x)) = u * x + -(u * y) := by ring
  calc
    _ = (∑ t : K, ∑ x ∈ E, if x + t ∈ E then χ (-(u * t)) else 0) /
        (E.card : ℂ) / (Fintype.card K : ℂ) := by
      unfold coordinateFourier meanC
      simp_rw [hpoint, div_eq_mul_inv, ← Finset.sum_mul]
    _ = (∑ x ∈ E, ∑ y ∈ E, χ (-(u * (y - x)))) / (E.card : ℂ) / (Fintype.card K : ℂ) := by
      rw [Finset.sum_comm]
      simp_rw [translate_character_sum χ E u]
    _ = ((∑ x ∈ E, χ (u * x)) * conj (∑ y ∈ E, χ (u * y))) /
        (E.card : ℂ) / (Fintype.card K : ℂ) := by
      simp_rw [hphase, hadd, character_neg_eq_conj χ hzero hnorm hadd,
        ← Finset.mul_sum, ← Finset.sum_mul, map_sum]
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast <;> rfl

/-- The positive Fourier coefficients sum to the value at zero, so the Fourier
ℓ¹ norm of the cutoff is one regardless of the size of its support. -/
theorem triangleCutoff_fourier_l1 {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hnorm : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hnontrivial : ∃ x, χ x ≠ 1)
    {E : Finset K} (hE : E.Nonempty) :
    (∑ u, ‖coordinateFourier χ (triangleCutoff E) u‖) = 1 := by
  have hnorm_re (u : K) : ‖coordinateFourier χ (triangleCutoff E) u‖ =
      (coordinateFourier χ (triangleCutoff E) u).re := by
    rw [triangleCutoff_fourier χ hzero hnorm hadd, Complex.ofReal_re]
    exact Complex.norm_of_nonneg (by positivity)
  have h := congrArg Complex.re (coordinateFourier_inversion χ hzero hadd hnontrivial
    (triangleCutoff E) 0)
  simpa only [triangleCutoff_zero hE, mul_zero, hzero, mul_one, Complex.one_re,
    Complex.re_sum, hnorm_re] using h.symm

/-- Translating a cutoff introduces only a phase in each Fourier coefficient. -/
theorem coordinateFourier_translate {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (A : K → ℂ) (c u : K) :
    coordinateFourier χ (fun t => A (t - c)) u = χ (-(u * c)) * coordinateFourier χ A u := by
  unfold coordinateFourier meanC
  have hphase (x : K) : -(u * (x + c)) = -(u * c) + -(u * x) := by ring
  have hsum : (∑ t, A (t - c) * χ (-(u * t))) =
      ∑ x, χ (-(u * c)) * (A x * χ (-(u * x))) := by
    calc
      _ = ∑ x, A (x + c - c) * χ (-(u * (x + c))) :=
        (Equiv.sum_comp (Equiv.addRight c) (fun t => A (t - c) * χ (-(u * t)))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [add_sub_cancel_right, hphase, hadd]
        ring
  rw [hsum, ← Finset.mul_sum, mul_div_assoc]

theorem triangleCutoff_translate_fourier_l1 {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hnorm : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hnontrivial : ∃ x, χ x ≠ 1)
    {E : Finset K} (hE : E.Nonempty) (c : K) :
    (∑ u, ‖coordinateFourier χ (fun t => triangleCutoff E (t - c)) u‖) = 1 := by
  simp_rw [coordinateFourier_translate χ hadd, norm_mul, hnorm, one_mul]
  exact triangleCutoff_fourier_l1 χ hzero hnorm hadd hnontrivial hE

theorem triangleCutoff_re_eq {K : Type*} [Add K] (E : Finset K) (t : K) :
    (triangleCutoff E t).re = ((E.filter fun x => x + t ∈ E).card : ℝ) / (E.card : ℝ) := by
  unfold triangleCutoff
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.ofReal_re]

theorem triangleCutoff_re_bounds {K : Type*} [Add K] (E : Finset K) (t : K) :
    0 ≤ (triangleCutoff E t).re ∧ (triangleCutoff E t).re ≤ 1 := by
  rw [triangleCutoff_re_eq]
  refine ⟨by positivity, ?_⟩
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun x => x + t ∈ E) E)

/-- Two translated triangle cutoffs introduce no Fourier norm loss in the
six-form finite-field correlation. -/
theorem triangle_weights_gowers_bound {K : Type*} [Field K] [Fintype K]
    (χ : K → ℂ) (hzero : χ 0 = 1) (hnorm : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hnontrivial : ∃ x, χ x ≠ 1)
    (g₁ g₂ : BoundedAffineWeight K) (gs : List (BoundedAffineWeight K)) (hlen : gs.length = 3)
    (hdet : g₁.dir.a * g₂.dir.b - g₁.dir.b * g₂.dir.a ≠ 0)
    (d : LinearDirection K) (c : K) (f : K → ℂ)
    (h : ∀ g ∈ g₁ :: g₂ :: gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0)
    {E F : Finset K} (hE : E.Nonempty) (hF : F.Nonempty) (s t : K)
    {G : ℝ} (hG : 0 ≤ G) (hf : gowersCubeMoment 5 f ≤ G ^ 32) :
    ‖meanC (fun x : K × K => triangleCutoff E (x.1 - s) * triangleCutoff F (x.2 - t) *
      (f (linearRow d.a d.b x + c) * affineWeightProduct x (g₁ :: g₂ :: gs)))‖ ≤ G := by
  let A := fun x => triangleCutoff E (x - s)
  let B := fun x => triangleCutoff F (x - t)
  have hsumA := triangleCutoff_translate_fourier_l1 χ hzero hnorm hadd hnontrivial hE s
  have hsumB := triangleCutoff_translate_fourier_l1 χ hzero hnorm hadd hnontrivial hF t
  have hresult := coordinate_weights_gowers_bound χ hnorm hadd g₁ g₂ gs hlen hdet d c f A B
    (coordinateFourier χ A) (coordinateFourier χ B) h
    (coordinateFourier_inversion χ hzero hadd hnontrivial A)
    (coordinateFourier_inversion χ hzero hadd hnontrivial B) hG hf
  simpa only [A, B, hsumA, hsumB, one_mul] using hresult

end Jsp000881
