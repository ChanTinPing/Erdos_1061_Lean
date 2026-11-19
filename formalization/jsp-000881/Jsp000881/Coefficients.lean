module

public import Jsp000881.Local
import all Jsp000881.Local
public import Mathlib.Tactic.ClearExcept

public section

namespace Jsp000881

open Filter

/-- The affine form coefficients in the original integer lattice coordinates. -/
def integralRow (θ : PlaneIndex) (i : Fin 6) : Plane.AffineRow ℤ :=
  ⟨(sextupleOn θ (0, 0)).coord i, (Plane.direction θ.1 θ.2.1 θ.2.2 i).1,
    (Plane.direction θ.1 θ.2.1 θ.2.2 i).2⟩

theorem integralRow_eval (θ : PlaneIndex) (nm : ℤ × ℤ) (i : Fin 6) :
    (integralRow θ i).eval nm.1 nm.2 = (sextupleOn θ nm).coord i :=
  (Plane.point_affine θ.1 θ.2.1 θ.2.2 nm.1 nm.2 i).symm

private theorem point_at_small_indices {θ : PlaneIndex} {z n m : ℤ}
    (hz : 1 ≤ z) (hθ : ParameterBox θ z) (hn : 0 ≤ n) (hn' : n ≤ 1)
    (hm : 0 ≤ m) (hm' : m ≤ 1) (i : Fin 6) :
    |(sextupleOn θ (n, m)).coord i| ≤ 1000000000 * (z * z) := by
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := hθ
  let α := Plane.W * θ.1
  let β := Plane.W * θ.2.1
  let γ := Plane.W * θ.2.2
  change z * z ≤ α at ha
  change α ≤ 2 * (z * z) at ha'
  change z ≤ β at hb
  change β ≤ 2 * z at hb'
  change z ≤ γ at hc
  change γ ≤ 2 * z at hc'
  let r : ℤ := 15 * (508 * n)
  let s : ℤ := 31 * (3918 + 508 * m)
  let t : ℤ := -1 - β * r - γ * s
  let v := sextupleOn θ (n, m)
  have hr0 : 0 ≤ r := by dsimp [r]; clear * - hn; omega
  have hr : r ≤ 7620 := by dsimp [r]; clear * - hn'; omega
  have hs0 : 0 ≤ s := by dsimp [s]; clear * - hm; omega
  have hs : s ≤ 137206 := by dsimp [s]; clear * - hm'; omega
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have ha0 : 0 ≤ α := (mul_self_nonneg z).trans ha
  have hb0 : 0 ≤ β := hz0.trans hb
  have hc0 : 0 ≤ γ := hz0.trans hc
  have ht0 : t ≤ 0 := by
    have hbr := mul_nonneg hb0 hr0
    have hcs := mul_nonneg hc0 hs0
    dsimp only [t]
    clear * - hbr hcs
    omega
  have ht : |t| ≤ 290000 * z := by
    rw [abs_of_nonpos ht0]
    have hz2 : 0 ≤ 2 * z := mul_nonneg (by decide) hz0
    have hbr := mul_le_mul hb' hr hr0 hz2
    have hcs := mul_le_mul hc' hs hs0 hz2
    dsimp only [t]
    nlinarith only [hbr, hcs, hz]
  have hzsq : z ≤ z * z := by
    simpa using mul_le_mul_of_nonneg_right hz hz0
  have hB0 : 0 ≤ 462 * β + 1 := by clear * - hb0; omega
  have hC0 : 0 ≤ 462 * γ + 1 := by clear * - hc0; omega
  have hB : 462 * β + 1 ≤ 925 * z := by clear * - hb' hz; omega
  have hC : 462 * γ + 1 ≤ 925 * z := by clear * - hc' hz; omega
  have h1 : |v.p1| ≤ 300000 * z := by
    change |508 * n + t| ≤ _
    calc
      _ ≤ |508 * n| + |t| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by clear * - hn; omega : 0 ≤ 508 * n)]
        clear * - hz hn' ht
        omega
  have h3 : |v.p3| ≤ 300000 * z := by
    change |3918 + 508 * m + t| ≤ _
    calc
      _ ≤ |3918 + 508 * m| + |t| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by clear * - hm; omega : 0 ≤ 3918 + 508 * m)]
        clear * - hz hm' ht
        omega
  have hz925 : 0 ≤ 925 * z := mul_nonneg (by decide) hz0
  have h2 : |v.p2| ≤ 300000000 * (z * z) := by
    have he : v.p2 = α * s + (462 * β + 1) * t := by
      change α * s + 462 * Plane.W * θ.2.1 * t + t = _
      dsimp only [β]
      ring
    rw [he]
    calc
      _ ≤ |α * s| + |(462 * β + 1) * t| := abs_add_le _ _
      _ = α * s + (462 * β + 1) * |t| := by
        rw [abs_of_nonneg (mul_nonneg ha0 hs0), abs_mul, abs_of_nonneg hB0]
      _ ≤ _ := by
        have hleft := mul_le_mul ha' hs hs0 (by positivity : 0 ≤ 2 * (z * z))
        have hright := mul_le_mul hB ht (abs_nonneg t) hz925
        nlinarith only [hleft, hright]
  have h4 : |v.p4| ≤ 300000000 * (z * z) := by
    have he : v.p4 = -(α * r) + (462 * γ + 1) * t := by
      change -(α * r) + 462 * Plane.W * θ.2.2 * t + t = _
      dsimp only [γ]
      ring
    rw [he]
    calc
      _ ≤ |-(α * r)| + |(462 * γ + 1) * t| := abs_add_le _ _
      _ = α * r + (462 * γ + 1) * |t| := by
        rw [abs_neg, abs_of_nonneg (mul_nonneg ha0 hr0), abs_mul, abs_of_nonneg hC0]
      _ ≤ _ := by
        have hleft := mul_le_mul ha' hr hr0 (by positivity : 0 ≤ 2 * (z * z))
        have hright := mul_le_mul hC ht (abs_nonneg t) hz925
        nlinarith only [hleft, hright]
  have h5 : |v.p5| ≤ 290000 * z := ht
  have h6 : |v.p6| ≤ 1000000000 * (z * z) := by
    have he : 508 * v.p6 = 15 * (v.p1 + v.p2) + 31 * (v.p3 + v.p4) - 508 * v.p5 - 462 :=
      Plane.point_sixth θ.1 θ.2.1 θ.2.2 n m
    have htri (a b c d : ℤ) :
        |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
      calc
        _ ≤ |a + b - c| + |d| := abs_sub _ _
        _ ≤ (|a + b| + |c|) + |d| := add_le_add (abs_sub _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    have hscaled : 508 * |v.p6| ≤ 508 * (1000000000 * (z * z)) := by
      calc
        _ = |508 * v.p6| := by rw [abs_mul, abs_of_nonneg (by decide : (0 : ℤ) ≤ 508)]
        _ ≤ |15 * (v.p1 + v.p2)| + |31 * (v.p3 + v.p4)| + |508 * v.p5| + |(462 : ℤ)| := by
          rw [he]
          exact htri _ _ _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
          have h12 := abs_add_le v.p1 v.p2
          have h34 := abs_add_le v.p3 v.p4
          have hzsq1 : 1 ≤ z * z := hz.trans hzsq
          linarith only [h1, h2, h3, h4, h5, h12, h34, hzsq, hzsq1]
    exact (mul_le_mul_iff_of_pos_left (by decide : (0 : ℤ) < 508)).mp hscaled
  change |v.coord i| ≤ _
  fin_cases i <;> simp only [Plane.Sextuple.coord]
  · change |v.p1| ≤ _
    exact h1.trans (by linarith only [hzsq, mul_self_nonneg z])
  · change |v.p2| ≤ _
    exact h2.trans (by linarith only [mul_self_nonneg z])
  · change |v.p3| ≤ _
    exact h3.trans (by linarith only [hzsq, mul_self_nonneg z])
  · change |v.p4| ≤ _
    exact h4.trans (by linarith only [mul_self_nonneg z])
  · change |v.p5| ≤ _
    exact h5.trans (by linarith only [hzsq, mul_self_nonneg z])
  · exact h6

theorem integralRow_bound {θ : PlaneIndex} {z : ℤ} (hz : 1 ≤ z) (hθ : ParameterBox θ z)
    (i : Fin 6) :
    |(integralRow θ i).constant| ≤ 2000000000 * (z * z) ∧
    |(integralRow θ i).left| ≤ 2000000000 * (z * z) ∧
    |(integralRow θ i).right| ≤ 2000000000 * (z * z) := by
  have h0 := point_at_small_indices hz hθ (n := 0) (m := 0) (by decide) (by decide)
    (by decide) (by decide) i
  have h1 := point_at_small_indices hz hθ (n := 1) (m := 0) (by decide) (by decide)
    (by decide) (by decide) i
  have h2 := point_at_small_indices hz hθ (n := 0) (m := 1) (by decide) (by decide)
    (by decide) (by decide) i
  constructor
  · exact h0.trans (by linarith only [mul_self_nonneg z])
  · constructor
    · change |(sextupleOn θ (1, 0)).coord i - (sextupleOn θ (0, 0)).coord i| ≤ _
      exact (abs_sub _ _).trans (by linarith only [h0, h1])
    · change |(sextupleOn θ (0, 1)).coord i - (sextupleOn θ (0, 0)).coord i| ≤ _
      exact (abs_sub _ _).trans (by linarith only [h0, h2])

/-- The distinct coefficient rows never become parallel, using the fixed
integer lattice directions employed by the prime estimate. -/
theorem integralRow_det_ne_zero {θ : PlaneIndex} {z : ℤ} (hz : 100 ≤ z) (hθ : ParameterBox θ z)
    {i j : Fin 6} (hne : i ≠ j) :
    (integralRow θ i).left * (integralRow θ j).right -
      (integralRow θ i).right * (integralRow θ j).left ≠ 0 := by
  obtain ⟨ha, _, hb, hb', hc, hc'⟩ := hθ
  exact Plane.directionDet_ne_zero θ.1 θ.2.1 θ.2.2 z hz ha hb hb' hc hc' hne

private theorem eventually_polylog_margin :
    ∀ᶠ k : ℕ in atTop,
      2000000000 * (k : ℝ) ^ 14 ≤ Real.log ((2 : ℝ) ^ k) ^ 16 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log 2 ^ 16 := pow_pos hlog _
  have hbig := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (2000000000 / Real.log 2 ^ 16)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hbig] with k hk hbig'
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkw : (2000000000 : ℝ) ≤ (k : ℝ) * Real.log 2 ^ 16 :=
    (div_le_iff₀ hL).mp hbig'
  have hksq : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ hk' (by decide)
  have hlarge := hkw.trans (mul_le_mul_of_nonneg_right hksq hL.le)
  calc
    _ ≤ ((k : ℝ) ^ 2 * Real.log 2 ^ 16) * (k : ℝ) ^ 14 :=
      mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = _ := by rw [Real.log_pow]; ring

/-- All three coefficients of each exact affine form fit the power-sixteen
logarithmic bound at the dyadic rectangle heights. -/
theorem eventually_integralRow_polylog :
    ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
      ParameterBox θ ((k : ℤ) ^ 7) → ∀ i : Fin 6,
      ((|(integralRow θ i).constant| : ℤ) : ℝ) ≤ Real.log ((2 : ℝ) ^ k) ^ 16 ∧
      ((|(integralRow θ i).left| : ℤ) : ℝ) ≤ Real.log ((2 : ℝ) ^ k) ^ 16 ∧
      ((|(integralRow θ i).right| : ℤ) : ℝ) ≤ Real.log ((2 : ℝ) ^ k) ^ 16 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_polylog_margin] with k hk hmain
  intro θ hθ i
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hs : (1 : ℤ) ≤ (k : ℤ) ^ 7 := one_le_pow₀ hkz
  obtain ⟨hc, hl, hr⟩ := integralRow_bound hs hθ i
  have upper : ((2000000000 * ((k : ℤ) ^ 7 * (k : ℤ) ^ 7) : ℤ) : ℝ) ≤
      Real.log ((2 : ℝ) ^ k) ^ 16 := by
    convert hmain using 1 <;> push_cast <;> ring
  exact ⟨(Int.cast_le.mpr hc).trans upper, (Int.cast_le.mpr hl).trans upper,
    (Int.cast_le.mpr hr).trans upper⟩

/-- At the selected heights the whole integer rectangle lies in the
ambient square of radius `T`. -/
theorem latticeRectangle_subset_square {T : ℤ} (hT : 8 ≤ T) {nm : ℤ × ℤ}
    (hnm : nm ∈ latticeRectangle T) : |nm.1| ≤ T ∧ |nm.2| ≤ T := by
  obtain ⟨h1, h2, h3, h4⟩ := (mem_latticeRectangle (by omega)).mp hnm
  exact ⟨abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr ⟨by omega, by omega⟩⟩

end Jsp000881
