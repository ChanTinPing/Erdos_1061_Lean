module

public import Jsp000881.GowersIteration
import all Jsp000881.GowersIteration
public import Jsp000881.Products
import all Jsp000881.Products
public import Jsp000881.Scaled
import all Jsp000881.Scaled

public section

namespace Jsp000881

open Filter

def integralRowDet (θ : PlaneIndex) (i j : Fin 6) : ℤ :=
  (integralRow θ i).left * (integralRow θ j).right -
    (integralRow θ i).right * (integralRow θ j).left

/-- A common bound for the absolute determinants in a parameter box. -/
def determinantBound (z : ℤ) : ℤ := 2 * (2000000000 * (z * z)) ^ 2

theorem abs_integralRowDet_le {θ : PlaneIndex} {z : ℤ}
    (hz : 1 ≤ z) (hθ : ParameterBox θ z) (i j : Fin 6) :
    |integralRowDet θ i j| ≤ determinantBound z := by
  let B : ℤ := 2000000000 * (z * z)
  have hB : 0 ≤ B := mul_nonneg (by decide) (mul_self_nonneg z)
  obtain ⟨_, hiL, hiR⟩ := integralRow_bound hz hθ i
  obtain ⟨_, hjL, hjR⟩ := integralRow_bound hz hθ j
  calc
    |integralRowDet θ i j| ≤ |(integralRow θ i).left * (integralRow θ j).right| +
        |(integralRow θ i).right * (integralRow θ j).left| := abs_sub _ _
    _ = |(integralRow θ i).left| * |(integralRow θ j).right| +
        |(integralRow θ i).right| * |(integralRow θ j).left| := by
      rw [abs_mul, abs_mul]
    _ ≤ B * B + B * B := add_le_add
      (mul_le_mul hiL hjR (abs_nonneg _) hB)
      (mul_le_mul hiR hjL (abs_nonneg _) hB)
    _ = determinantBound z := by simp only [determinantBound, ← pow_two, two_mul, B]

theorem integralRowMod_det_eq_cast (p : ℕ) (θ : PlaneIndex) (i j : Fin 6) :
    (integralRowMod θ p i).left * (integralRowMod θ p j).right -
        (integralRowMod θ p i).right * (integralRowMod θ p j).left =
      (integralRowDet θ i j : ZMod p) := by
  simp only [integralRowMod, integralRowDet, Int.cast_sub, Int.cast_mul]

/-- A nonzero integral determinant remains nonzero modulo every modulus
strictly greater than its absolute value. -/
theorem integralRowMod_det_ne_zero {p : ℕ} {θ : PlaneIndex} {z : ℤ} {i j : Fin 6}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hij : i ≠ j)
    (hp : |integralRowDet θ i j| < (p : ℤ)) :
    (integralRowMod θ p i).left * (integralRowMod θ p j).right -
      (integralRowMod θ p i).right * (integralRowMod θ p j).left ≠ 0 := by
  rw [integralRowMod_det_eq_cast]
  intro hzero
  have hD : integralRowDet θ i j ≠ 0 := integralRow_det_ne_zero hz hθ hij
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (integralRowDet θ i j) p).mp hzero
  exact (not_lt_of_ge (Int.le_abs_of_dvd hD hdvd)) hp

theorem integralRowMod_pairwise_det_ne_zero {p : ℕ} {θ : PlaneIndex} {z : ℤ} {i j : Fin 6}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ)) (hij : i ≠ j) :
    (integralRowMod θ p i).left * (integralRowMod θ p j).right -
      (integralRowMod θ p i).right * (integralRowMod θ p j).left ≠ 0 :=
  integralRowMod_det_ne_zero hz hθ hij
    ((abs_integralRowDet_le ((by decide : (1 : ℤ) ≤ 100).trans hz) hθ i j).trans_lt hp)

private theorem integralRowMod_nonzero {p : ℕ} {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ)) (i : Fin 6) :
    (integralRowMod θ p i).left ≠ 0 ∨ (integralRowMod θ p i).right ≠ 0 := by
  have hother : ∃ j : Fin 6, i ≠ j := by
    by_cases hi : i = 0
    · refine ⟨1, ?_⟩
      rw [hi]
      decide
    · exact ⟨0, hi⟩
  obtain ⟨j, hij⟩ := hother
  by_cases hl : (integralRowMod θ p i).left = 0
  · right
    intro hr
    exact integralRowMod_pairwise_det_ne_zero hz hθ hp hij (by simp [hl, hr])
  · exact Or.inl hl

/-- The linear part of an integral row, viewed over the ambient prime field. -/
def integralRowDirection {p : ℕ} [Fact p.Prime] {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ)) (i : Fin 6) :
    LinearDirection (ZMod p) :=
  ⟨(integralRowMod θ p i).left, (integralRowMod θ p i).right, integralRowMod_nonzero hz hθ hp i⟩

theorem integralRowDirection_independent {p : ℕ} [Fact p.Prime] {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ))
    {i j : Fin 6} (hij : i ≠ j) :
    (integralRowDirection hz hθ hp i).a * (integralRowDirection hz hθ hp j).b -
      (integralRowDirection hz hθ hp i).b * (integralRowDirection hz hθ hp j).a ≠ 0 :=
  integralRowMod_pairwise_det_ne_zero hz hθ hp hij

theorem integralRowDirection_eval {p : ℕ} [Fact p.Prime] {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ))
    (i : Fin 6) (x : ZMod p × ZMod p) :
    linearRow (integralRowDirection hz hθ hp i).a (integralRowDirection hz hθ hp i).b x +
      (integralRowMod θ p i).constant = (integralRowMod θ p i).eval x.1 x.2 := by
  simp only [linearRow, integralRowDirection, Plane.AffineRow.eval]
  ring

/-- Apply the five-direction Cauchy–Schwarz estimate to the exact affine rows. -/
theorem integralRows_gowers_bound {p : ℕ} [Fact p.Prime] {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ))
    (i : Fin 6) (companions : List (Fin 6)) (hlen : companions.length = 5)
    (hi : i ∉ companions) (g : Fin 6 → ZMod p → ℂ) (hg : ∀ j u, ‖g j u‖ ≤ 1)
    (f : ZMod p → ℂ) :
    ‖meanC (fun x : ZMod p × ZMod p =>
      f ((integralRowMod θ p i).eval x.1 x.2) *
        (companions.map fun j => g j ((integralRowMod θ p j).eval x.1 x.2)).prod)‖ ^ 32 ≤
      gowersCubeMoment 5 f := by
  let w : Fin 6 → BoundedAffineWeight (ZMod p) := fun j =>
    ⟨integralRowDirection hz hθ hp j, (integralRowMod θ p j).constant, g j, hg j⟩
  have heval (j : Fin 6) (x : ZMod p × ZMod p) :
      (w j).eval x = g j ((integralRowMod θ p j).eval x.1 x.2) := by
    simp only [w, BoundedAffineWeight.eval, integralRowDirection_eval]
  have hproduct (L : List (Fin 6)) (x : ZMod p × ZMod p) :
      affineWeightProduct x (L.map w) =
        (L.map fun j => g j ((integralRowMod θ p j).eval x.1 x.2)).prod := by
    induction L with
    | nil => rfl
    | cons j L ih => simp only [List.map_cons, List.prod_cons, affineWeightProduct, heval, ih]
  have hdet : ∀ v ∈ companions.map w,
      v.dir.a * (integralRowDirection hz hθ hp i).b -
        v.dir.b * (integralRowDirection hz hθ hp i).a ≠ 0 := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact integralRowDirection_independent hz hθ hp (fun h : j = i => hi (h ▸ hj))
  have hbound := affine_system_gowers_bound 4 (companions.map w) (by simpa using hlen)
    (integralRowDirection hz hθ hp i) (integralRowMod θ p i).constant hdet f
  simpa only [integralRowDirection_eval, hproduct, show (2 : ℕ) ^ (4 + 1) = 32 by decide] using hbound

/-- Any prime at least the dyadic height is eventually larger than all the
absolute determinants at parameter scale `k^7`. -/
theorem eventually_determinantBound_lt_dyadicHeight :
    ∀ᶠ k : ℕ in atTop, determinantBound ((k : ℤ) ^ 7) < (2 : ℤ) ^ k := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 28 (r := (2 : ℝ)) (by norm_num)
  have hsmall := (tendsto_order.1 hlim).2 (1 / 8000000000000000000) (by norm_num)
  filter_upwards [hsmall] with k hk
  have hpow : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  change (k : ℝ) ^ 28 / (2 : ℝ) ^ k < 1 / 8000000000000000000 at hk
  have hlt : 8000000000000000000 * (k : ℝ) ^ 28 < (2 : ℝ) ^ k := by
    linarith only [(div_lt_iff₀ hpow).mp hk]
  have hcast : (determinantBound ((k : ℤ) ^ 7) : ℝ) =
      8000000000000000000 * (k : ℝ) ^ 28 := by
    unfold determinantBound
    push_cast
    ring
  have h : (determinantBound ((k : ℤ) ^ 7) : ℝ) < (((2 : ℤ) ^ k : ℤ) : ℝ) := by
    rw [hcast]
    exact_mod_cast hlt
  exact_mod_cast h

end Jsp000881
