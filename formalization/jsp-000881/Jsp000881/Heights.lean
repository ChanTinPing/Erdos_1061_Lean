module

public import Jsp000881.Plane
import all Jsp000881.Plane
public import Mathlib.Tactic.ClearExcept

/-!
# Heights on the fixed lattice rectangle

The first, third and fifth coordinates have scale `z * T`. The other
coordinates have scale `z^2 * T`. The perimeter bound is an integer
inequality so it can be applied before passing to the real counting function.
-/

public section

namespace Jsp000881.Plane

structure RectangleHeights (p : Sextuple) (z T : ℤ) : Prop where
  coordinate_large : ∀ i : Fin 6, 127 < p.coord i
  coordinate_upper : ∀ i : Fin 6, p.coord i ≤ 4000 * z * z * T
  first_order : p.p1 < p.p2
  second_order : p.p3 < p.p4
  third_order : p.p5 < p.p6
  perimeter_le : 508 * p.p5 * p.p6 ≤ 1000000 * z ^ 3 * T ^ 2

private theorem rectangleHeights_of_coordinates
    (p : Sextuple) (α β γ u v t z T : ℤ)
    (hz : 100 ≤ z) (hT : 3 ≤ T)
    (hα : z * z ≤ α) (hα' : α ≤ 2 * (z * z))
    (hβ : z ≤ β) (hβ' : β ≤ 2 * z)
    (hγ : z ≤ γ) (hγ' : γ ≤ 2 * z)
    (hu : T ≤ u) (hu' : u ≤ 2 * T) (hv : 0 ≤ v) (hv' : 100000 * v ≤ T)
    (ht : t = -1 + β * u - γ * v)
    (hp1 : 15 * (p.p1 - t) = -u)
    (hp2 : p.p2 = α * v + 462 * (β * t) + t)
    (hp3 : 31 * (p.p3 - t) = v)
    (hp4 : p.p4 = α * u + 462 * (γ * t) + t)
    (hp5 : p.p5 = t)
    (hp6 : 508 * p.p6 = 15 * (p.p1 + p.p2) + 31 * (p.p3 + p.p4) - 508 * t - 462) :
    RectangleHeights p z T := by
  have hz0 : 0 ≤ z := (by decide : (0 : ℤ) ≤ 100).trans hz
  have hT0 : 0 ≤ T := (by decide : (0 : ℤ) ≤ 3).trans hT
  have hα0 : 0 ≤ α := (mul_nonneg hz0 hz0).trans hα
  have hβ0 : 0 ≤ β := hz0.trans hβ
  have hγ0 : 0 ≤ γ := hz0.trans hγ
  have hu0 : 0 ≤ u := hT0.trans hu
  have hzSq : z ≤ z * z := by
    calc
      z = 1 * z := by ring
      _ ≤ z * z := mul_le_mul_of_nonneg_right (by clear * - hz; omega) hz0
  have hzT_le : z * T ≤ z * z * T := mul_le_mul_of_nonneg_right hzSq hT0
  have hHundredT : 100 * T ≤ z * T := mul_le_mul_of_nonneg_right hz hT0
  have hβu_lo : z * T ≤ β * u := mul_le_mul hβ hu hT0 hβ0
  have hβu_hi : β * u ≤ 4 * (z * T) := by
    calc
      β * u ≤ (2 * z) * (2 * T) := mul_le_mul hβ' hu' hu0 (by clear * - hz0; omega)
      _ = _ := by ring
  have hγv0 : 0 ≤ γ * v := mul_nonneg hγ0 hv
  have hγv_hi : 4 * (γ * v) ≤ z * T := by
    calc
      4 * (γ * v) = γ * (4 * v) := by ring
      _ ≤ (2 * z) * (4 * v) := mul_le_mul_of_nonneg_right hγ' (by clear * - hv; omega)
      _ = z * (8 * v) := by ring
      _ ≤ z * T := mul_le_mul_of_nonneg_left (by clear * - hv hv'; omega) hz0
  have ht_lo : z * T ≤ 2 * t := by
    clear * - ht hβu_lo hγv_hi hHundredT hT
    omega
  have ht_hi : t ≤ 4 * (z * T) := by
    clear * - ht hβu_hi hγv0
    omega
  have hTt : T ≤ t := by
    clear * - ht_lo hHundredT hT
    omega
  have ht0 : 0 ≤ t := hT0.trans hTt
  have ht_hi' : t ≤ 4 * (z * z * T) := by
    clear * - ht_hi hzT_le
    omega
  have hT_hi : T ≤ z * z * T := by
    clear * - hHundredT hzT_le hT0
    omega

  have hp1_lo : t - 2 * T ≤ p.p1 := by
    clear * - hp1 hu' hT0
    omega
  have hp1_hi : p.p1 ≤ t := by
    clear * - hp1 hu hT0
    omega
  have hp3_lo : t ≤ p.p3 := by
    clear * - hp3 hv
    omega
  have hp3_hi : p.p3 ≤ t + T := by
    clear * - hp3 hv' hT0
    omega
  have hp1_large : 127 < p.p1 := by
    clear * - hp1_lo ht_lo hHundredT hT
    omega
  have hp3_large : 127 < p.p3 := by
    clear * - hp3_lo ht_lo hHundredT hT
    omega
  have hp5_large : 127 < p.p5 := by
    clear * - hp5 ht_lo hHundredT hT
    omega

  have hαv0 : 0 ≤ α * v := mul_nonneg hα0 hv
  have hαu0 : 0 ≤ α * u := mul_nonneg hα0 hu0
  have hβt_lo : t ≤ β * t := by
    calc
      t = 1 * t := by ring
      _ ≤ β * t := mul_le_mul_of_nonneg_right (by clear * - hz hβ; omega) ht0
  have hγt_lo : t ≤ γ * t := by
    calc
      t = 1 * t := by ring
      _ ≤ γ * t := mul_le_mul_of_nonneg_right (by clear * - hz hγ; omega) ht0
  have hp2_lo : 463 * t ≤ p.p2 := by
    clear * - hp2 hαv0 hβt_lo
    omega
  have hp4_lo : 463 * t ≤ p.p4 := by
    clear * - hp4 hαu0 hγt_lo
    omega
  have hp12 : p.p1 < p.p2 := by
    clear * - hp2_lo hp1_hi hTt hT
    omega
  have hp34 : p.p3 < p.p4 := by
    clear * - hp4_lo hp3_hi hTt hT
    omega
  have hp2_large : 127 < p.p2 := hp1_large.trans hp12
  have hp4_large : 127 < p.p4 := hp3_large.trans hp34
  have hp56 : p.p5 < p.p6 := by
    clear * - hp5 hp6 hp1_lo hp2_lo hp3_lo hp4_lo hTt hT
    omega
  have hp6_large : 127 < p.p6 := hp5_large.trans hp56

  have hαv_hi : α * v ≤ 2 * (z * z * T) := by
    calc
      α * v ≤ (2 * (z * z)) * T :=
        mul_le_mul hα' (by clear * - hv hv'; omega) hv
          (mul_nonneg (by decide) (mul_self_nonneg z))
      _ = _ := by ring
  have hαu_hi : α * u ≤ 4 * (z * z * T) := by
    calc
      α * u ≤ (2 * (z * z)) * (2 * T) :=
        mul_le_mul hα' hu' hu0 (mul_nonneg (by decide) (mul_self_nonneg z))
      _ = _ := by ring
  have hβt_hi : β * t ≤ 8 * (z * z * T) := by
    calc
      β * t ≤ (2 * z) * (4 * (z * T)) := mul_le_mul hβ' ht_hi ht0 (by clear * - hz0; omega)
      _ = _ := by ring
  have hγt_hi : γ * t ≤ 8 * (z * z * T) := by
    calc
      γ * t ≤ (2 * z) * (4 * (z * T)) := mul_le_mul hγ' ht_hi ht0 (by clear * - hz0; omega)
      _ = _ := by ring
  have hscale_nonneg : 0 ≤ z * z * T := mul_nonneg (mul_nonneg hz0 hz0) hT0
  have hp1_top : p.p1 ≤ 5 * (z * z * T) := by
    clear * - hp1_hi ht_hi' hscale_nonneg
    omega
  have hp2_top : p.p2 ≤ 4000 * (z * z * T) := by
    clear * - hp2 hαv_hi hβt_hi ht_hi' hscale_nonneg
    omega
  have hp3_top : p.p3 ≤ 5 * (z * z * T) := by
    clear * - hp3_hi ht_hi' hT_hi
    omega
  have hp4_top : p.p4 ≤ 4000 * (z * z * T) := by
    clear * - hp4 hαu_hi hγt_hi ht_hi' hscale_nonneg
    omega
  have hp6_top : p.p6 ≤ 400 * (z * z * T) := by
    clear * - hp6 hp1_top hp2_top hp3_top hp4_top ht0 hscale_nonneg
    omega
  have hp5_top : p.p5 ≤ 4 * (z * T) := by
    clear * - hp5 ht_hi
    omega
  refine ⟨?_, ?_, hp12, hp34, hp56, ?_⟩
  · intro i
    fin_cases i
    · simpa [Sextuple.coord] using hp1_large
    · simpa [Sextuple.coord] using hp2_large
    · simpa [Sextuple.coord] using hp3_large
    · simpa [Sextuple.coord] using hp4_large
    · simpa [Sextuple.coord] using hp5_large
    · simpa [Sextuple.coord] using hp6_large
  · intro i
    rw [show (4000 : ℤ) * z * z * T = 4000 * (z * z * T) by ring]
    fin_cases i
    · change p.p1 ≤ 4000 * (z * z * T)
      clear * - hp1_top hscale_nonneg
      omega
    · exact hp2_top
    · change p.p3 ≤ 4000 * (z * z * T)
      clear * - hp3_top hscale_nonneg
      omega
    · exact hp4_top
    · change p.p5 ≤ 4000 * (z * z * T)
      clear * - hp5_top hzT_le hscale_nonneg
      omega
    · change p.p6 ≤ 4000 * (z * z * T)
      clear * - hp6_top hscale_nonneg
      omega
  · calc
      508 * p.p5 * p.p6 ≤ (508 * (4 * (z * T))) * (400 * (z * z * T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp5_top (by norm_num))
          hp6_top (by clear * - hp6_large; omega) (by positivity)
      _ = 812800 * (z ^ 3 * T ^ 2) := by ring
      _ ≤ 1000000 * (z ^ 3 * T ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring

/-- For the lattice rectangle `-2*T ≤ r ≤ -T` and `0 ≤ 100000*s ≤ T`, all
six coordinates exceed `127` and each prime pair is already ordered. -/
theorem point_rectangle_heights (a b c n m z T : ℤ)
    (hz : 100 ≤ z) (hT : 3 ≤ T)
    (ha : z * z ≤ W * a) (ha' : W * a ≤ 2 * (z * z))
    (hb : z ≤ W * b) (hb' : W * b ≤ 2 * z)
    (hc : z ≤ W * c) (hc' : W * c ≤ 2 * z)
    (hr : T ≤ -(15 * (508 * n))) (hr' : -(15 * (508 * n)) ≤ 2 * T)
    (hs : 0 ≤ 31 * (3918 + 508 * m)) (hs' : 100000 * (31 * (3918 + 508 * m)) ≤ T) :
    RectangleHeights (point a b c n m) z T := by
  let p := point a b c n m
  let u : ℤ := -(15 * (508 * n))
  let v : ℤ := 31 * (3918 + 508 * m)
  let t := p.p5
  refine rectangleHeights_of_coordinates p (W * a) (W * b) (W * c) u v t z T
    hz hT ha ha' hb hb' hc hc' hr hr' hs hs' ?_ ?_ ?_ ?_ ?_ rfl ?_
  · change -1 - W * b * (15 * (508 * n)) - W * c * v = -1 + W * b * u - W * c * v
    dsimp only [u]
    ring
  · simpa only [p, t, u, neg_neg] using
      congrArg (fun coordinate : ℤ => 15 * coordinate) (point_first_coordinate a b c n m)
  · change W * a * v + 462 * W * b * t + t = W * a * v + 462 * (W * b * t) + t
    ring
  · change 31 * ((point a b c n m).p3 - (point a b c n m).p5) = 31 * (3918 + 508 * m)
    rw [point_second_coordinate]
  · change -(W * a * (15 * (508 * n))) + 462 * W * c * t + t =
      W * a * u + 462 * (W * c * t) + t
    dsimp only [u]
    ring
  · exact point_sixth a b c n m

end Jsp000881.Plane
