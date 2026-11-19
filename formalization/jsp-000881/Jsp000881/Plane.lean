module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The fixed integral plane in the §3 construction

We use Li's ruling parameters `α = W*a`, `β = W*b`, `γ = W*c` and
the fixed lattice `y₁ = 508*n`, `y₃ = 3918 + 508*m`.  The expression
for the sixth coordinate is the exact polynomial quotient of its
defining numerator by `508`.
-/

public section

namespace Jsp000881.Plane

def P : ℤ := 2 * 3 * 5 * 7 * 11 * 31 * 127

def W : ℤ := 508 * P

structure Sextuple where
  p1 : ℤ
  p2 : ℤ
  p3 : ℤ
  p4 : ℤ
  p5 : ℤ
  p6 : ℤ

/-- Coordinates in the order of Li's six forms. -/
def Sextuple.coord (v : Sextuple) (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => v.p1
  | 1 => v.p2
  | 2 => v.p3
  | 3 => v.p4
  | 4 => v.p5
  | _ => v.p6

private def r (n : ℤ) : ℤ := 15 * (508 * n)

private def s (m : ℤ) : ℤ := 31 * (3918 + 508 * m)

def point (a b c n m : ℤ) : Sextuple :=
  let y1 := 508 * n
  let y3 := 3918 + 508 * m
  let x := r n
  let y := s m
  let t := -1 - W * b * x - W * c * y
  { p1 := y1 + t
    p2 := W * a * y + 462 * W * b * t + t
    p3 := y3 + t
    p4 := -(W * a * x) + 462 * W * c * t + t
    p5 := t
    p6 := 15 * n + 31 * m + 239 +
      P * (15 * a * y - 31 * a * x + 462 * (15 * b + 31 * c) * t +
        416 * (b * x + c * y)) }

theorem point_affine (a b c n m : ℤ) (i : Fin 6) :
    (point a b c n m).coord i = (point a b c 0 0).coord i +
      ((point a b c 1 0).coord i - (point a b c 0 0).coord i) * n +
      ((point a b c 0 1).coord i - (point a b c 0 0).coord i) * m := by
  fin_cases i <;> simp [Sextuple.coord, point, r, s] <;> ring

/-- The linear coefficients in the two fixed lattice coordinates. -/
def direction (a b c : ℤ) (i : Fin 6) : ℤ × ℤ :=
  ((point a b c 1 0).coord i - (point a b c 0 0).coord i,
    (point a b c 0 1).coord i - (point a b c 0 0).coord i)

def directionDet (a b c : ℤ) (i j : Fin 6) : ℤ :=
  (direction a b c i).1 * (direction a b c j).2 -
    (direction a b c i).2 * (direction a b c j).1

/-- Determinants for the pair with `i < j`, after the fixed lattice change of variables. -/
private def factoredDet (α β γ : ℤ) (i j : Fin 6) : ℤ :=
  let h := 15 * β + 31 * γ - 1
  let p := 31 * α - 462 * β - 1
  let q := 15 * α + 462 * γ + 1
  let l := α + β - γ
  match i.val, j.val with
  | 0, 1 => -(31 * 508 ^ 2 * (15 * α * β - α + 462 * β * γ + γ))
  | 0, 2 => -(508 ^ 2 * h)
  | 0, 3 => -(31 * 508 ^ 2 * γ * q)
  | 0, 4 => -(31 * 508 ^ 2 * γ)
  | 0, 5 => -(31 * 508 * q * h)
  | 1, 2 => 15 * 508 ^ 2 * β * p
  | 1, 3 => 465 * 508 ^ 2 * α * l
  | 1, 4 => 465 * 508 ^ 2 * α * β
  | 1, 5 => 465 * 508 * l * p
  | 2, 3 => -(15 * 508 ^ 2 * (31 * α * γ - α - 462 * β * γ - β))
  | 2, 4 => 15 * 508 ^ 2 * β
  | 2, 5 => -(15 * 508 * p * h)
  | 3, 4 => 465 * 508 ^ 2 * α * γ
  | 3, 5 => -(465 * 508 * l * q)
  | 4, 5 => -(465 * 508 * (15 * α * β + 31 * α * γ + β - γ))
  | _, _ => 0

private theorem directionDet_eq (a b c : ℤ) {i j : Fin 6} (hij : i < j) :
    directionDet a b c i j = factoredDet (W * a) (W * b) (W * c) i j := by
  have hv : i.val < j.val := hij
  clear hij
  fin_cases i <;> fin_cases j <;> norm_num at hv
  all_goals simp [directionDet, direction, factoredDet, Sextuple.coord, point, r, s, W] <;> ring

/-- Each pair of the six affine forms has independent directions in the parameter box. -/
theorem directionDet_ne_zero_of_lt (a b c z : ℤ) (hz : 100 ≤ z)
    (ha : z * z ≤ W * a) (hb : z ≤ W * b) (hb' : W * b ≤ 2 * z)
    (hc : z ≤ W * c) (hc' : W * c ≤ 2 * z) {i j : Fin 6} (hij : i < j) :
    directionDet a b c i j ≠ 0 := by
  let α := W * a
  let β := W * b
  let γ := W * c
  change z * z ≤ α at ha
  change z ≤ β at hb
  change β ≤ 2 * z at hb'
  change z ≤ γ at hc
  change γ ≤ 2 * z at hc'
  have hz0 : 0 ≤ z := by omega
  have hsq : 100 * z ≤ z * z := by
    have hprod : 0 ≤ z * (z - 100) := mul_nonneg hz0 (sub_nonneg.mpr hz)
    rw [mul_sub, mul_comm z 100] at hprod
    exact sub_nonneg.mp hprod
  have ha0 : 0 < α := by omega
  have hb0 : 0 < β := by omega
  have hc0 : 0 < γ := by omega
  have hh : 0 < 15 * β + 31 * γ - 1 := by omega
  have hp : 0 < 31 * α - 462 * β - 1 := by omega
  have hq : 0 < 15 * α + 462 * γ + 1 := by omega
  have hl : 0 < α + β - γ := by omega
  have hd12 : 0 < 15 * α * β - α + 462 * β * γ + γ := by
    calc
      0 < α * (15 * β - 1) + (462 * β + 1) * γ :=
        add_pos (mul_pos ha0 (by omega)) (mul_pos (by omega) hc0)
      _ = _ := by ring
  have hd34 : 0 < 31 * α * γ - α - 462 * β * γ - β := by
    calc
      0 < (α - 50 * β) * (31 * γ - 1) + β * (1088 * γ - 51) :=
        add_pos_of_nonneg_of_pos (mul_nonneg (by omega) (by omega)) (mul_pos hb0 (by omega))
      _ = _ := by ring
  have hd56 : 0 < 15 * α * β + 31 * α * γ + β - γ := by
    calc
      0 < 15 * α * β + (31 * α - 1) * γ + β :=
        add_pos (add_pos (mul_pos (by omega) hb0) (mul_pos (by omega) hc0)) hb0
      _ = _ := by ring
  rw [directionDet_eq a b c hij]
  change factoredDet α β γ i j ≠ 0
  have hv : i.val < j.val := hij
  clear hij
  fin_cases i <;> fin_cases j <;> norm_num at hv
  all_goals
    simp only [factoredDet, neg_ne_zero]
    exact ne_of_gt (by positivity)

theorem directionDet_ne_zero (a b c z : ℤ) (hz : 100 ≤ z)
    (ha : z * z ≤ W * a) (hb : z ≤ W * b) (hb' : W * b ≤ 2 * z)
    (hc : z ≤ W * c) (hc' : W * c ≤ 2 * z) {i j : Fin 6} (hij : i ≠ j) :
    directionDet a b c i j ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hl | hr
  · exact directionDet_ne_zero_of_lt a b c z hz ha hb hb' hc hc' hl
  · have hflip : directionDet a b c i j = -directionDet a b c j i := by
      unfold directionDet
      ring
    rw [hflip, neg_ne_zero]
    exact directionDet_ne_zero_of_lt a b c z hz ha hb hb' hc hc' hr

/-- The intersection of a coordinate-coincidence line with a finite lattice region. -/
def coordinateCollisions (a b c : ℤ) (i j : Fin 6) (box : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  box.filter fun nm => (point a b c nm.1 nm.2).coord i = (point a b c nm.1 nm.2).coord j

private theorem collision_equation {a b c n m : ℤ} {i j : Fin 6}
    (h : (point a b c n m).coord i = (point a b c n m).coord j) :
    ((direction a b c i).1 - (direction a b c j).1) * n +
      ((direction a b c i).2 - (direction a b c j).2) * m =
        (point a b c 0 0).coord j - (point a b c 0 0).coord i := by
  simp only [direction]
  linear_combination h - (point_affine a b c n m i) + (point_affine a b c n m j)

theorem card_coordinateCollisions_le (a b c : ℤ) (i j : Fin 6) (box : Finset (ℤ × ℤ))
    (hdet : directionDet a b c i j ≠ 0) :
    (coordinateCollisions a b c i j box).card ≤
      max (box.image Prod.fst).card (box.image Prod.snd).card := by
  let collisions := coordinateCollisions a b c i j box
  change collisions.card ≤ _
  have hmem {x : ℤ × ℤ} (hx : x ∈ collisions) : x ∈ box ∧
      (point a b c x.1 x.2).coord i = (point a b c x.1 x.2).coord j :=
    Finset.mem_filter.mp hx
  by_cases hm : (direction a b c i).2 = (direction a b c j).2
  · have hn : (direction a b c i).1 ≠ (direction a b c j).1 := by
      intro h
      apply hdet
      unfold directionDet
      rw [h, hm]
      ring
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (le_max_right _ _)
    · intro x hx
      exact Finset.mem_image_of_mem Prod.snd (hmem hx).1
    · intro x hx y hy hxy
      change x.2 = y.2 at hxy
      have eqx := collision_equation (hmem hx).2
      have eqy := collision_equation (hmem hy).2
      rw [hxy] at eqx
      have hprod : ((direction a b c i).1 - (direction a b c j).1) * (x.1 - y.1) = 0 := by
        linear_combination eqx - eqy
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hn))) hxy
  · refine le_trans (Finset.card_le_card_of_injOn Prod.fst ?_ ?_) (le_max_left _ _)
    · intro x hx
      exact Finset.mem_image_of_mem Prod.fst (hmem hx).1
    · intro x hx y hy hxy
      change x.1 = y.1 at hxy
      have eqx := collision_equation (hmem hx).2
      have eqy := collision_equation (hmem hy).2
      rw [hxy] at eqx
      have hprod : ((direction a b c i).2 - (direction a b c j).2) * (x.2 - y.2) = 0 := by
        linear_combination eqx - eqy
      exact Prod.ext hxy (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hm)))

theorem point_sixth (a b c n m : ℤ) :
    508 * (point a b c n m).p6 =
      15 * ((point a b c n m).p1 + (point a b c n m).p2) +
      31 * ((point a b c n m).p3 + (point a b c n m).p4) -
      508 * (point a b c n m).p5 - 462 := by
  simp only [point, r, s, W]
  ring

theorem point_numerator_dvd (a b c n m : ℤ) :
    (508 : ℤ) ∣
      15 * ((point a b c n m).p1 + (point a b c n m).p2) +
      31 * ((point a b c n m).p3 + (point a b c n m).p4) -
      508 * (point a b c n m).p5 - 462 :=
  ⟨(point a b c n m).p6, (point_sixth a b c n m).symm⟩

theorem point_sum (a b c n m : ℤ) :
    15 * ((point a b c n m).p1 + (point a b c n m).p2) +
      31 * ((point a b c n m).p3 + (point a b c n m).p4) =
      508 * ((point a b c n m).p5 + (point a b c n m).p6) + 462 := by
  simp only [point, r, s, W]
  ring

theorem point_product (a b c n m : ℤ) :
    15 * (point a b c n m).p1 * (point a b c n m).p2 +
      31 * (point a b c n m).p3 * (point a b c n m).p4 =
      508 * (point a b c n m).p5 * (point a b c n m).p6 := by
  simp only [point, r, s, W]
  ring

theorem point_shifted_product (a b c n m : ℤ) :
    15 * ((point a b c n m).p1 + 1) * ((point a b c n m).p2 + 1) +
      31 * ((point a b c n m).p3 + 1) * ((point a b c n m).p4 + 1) =
      508 * ((point a b c n m).p5 + 1) * ((point a b c n m).p6 + 1) := by
  linear_combination (point_product a b c n m) + (point_sum a b c n m)

theorem point_first_coordinate (a b c n m : ℤ) :
    (point a b c n m).p1 - (point a b c n m).p5 = 508 * n := by
  simp only [point]
  ring

theorem point_second_coordinate (a b c n m : ℤ) :
    (point a b c n m).p3 - (point a b c n m).p5 = 3918 + 508 * m := by
  simp only [point]
  ring

theorem lattice_coordinates_of_eq {a b c a' b' c' n m n' m' : ℤ}
    (h : point a b c n m = point a' b' c' n' m') : (n, m) = (n', m') := by
  apply Prod.ext
  · have hv := congrArg (fun z : Sextuple => z.p1 - z.p5) h
    change (point a b c n m).p1 - (point a b c n m).p5 =
      (point a' b' c' n' m').p1 - (point a' b' c' n' m').p5 at hv
    rw [point_first_coordinate, point_first_coordinate] at hv
    change n = n'
    omega
  · have hv := congrArg (fun z : Sextuple => z.p3 - z.p5) h
    change (point a b c n m).p3 - (point a b c n m).p5 =
      (point a' b' c' n' m').p3 - (point a' b' c' n' m').p5 at hv
    rw [point_second_coordinate, point_second_coordinate] at hv
    change m = m'
    omega

theorem point_injective (a b c : ℤ) :
    Function.Injective (fun nm : ℤ × ℤ => point a b c nm.1 nm.2) := by
  intro x y h
  exact lattice_coordinates_of_eq h

theorem point_zero_residues (a b c : ℤ) :
    (P ∣ (point a b c 0 0).p1 - (-1)) ∧
      (P ∣ (point a b c 0 0).p2 - (-1)) ∧
      (P ∣ (point a b c 0 0).p3 - 3917) ∧
      (P ∣ (point a b c 0 0).p4 - (-1)) ∧
      (P ∣ (point a b c 0 0).p5 - (-1)) ∧
      (P ∣ (point a b c 0 0).p6 - 239) := by
  let y : ℤ := 31 * 3918
  let t : ℤ := -1 - W * c * y
  refine ⟨⟨-(508 * c * y), ?_⟩,
    ⟨508 * (a * y + 462 * b * t - c * y), ?_⟩,
    ⟨-(508 * c * y), ?_⟩,
    ⟨508 * (462 * c * t - c * y), ?_⟩,
    ⟨-(508 * c * y), ?_⟩,
    ⟨15 * a * y + 462 * (15 * b + 31 * c) * t + 416 * c * y, ?_⟩⟩ <;>
    simp only [point, t, y, r, s, W] <;> ring

private theorem nondiv_of_residue {p x y : ℤ} (h : p ∣ x - y) (hy : ¬ p ∣ y) : ¬ p ∣ x := by
  intro hx
  have hd := dvd_sub hx h
  have he : x - (x - y) = y := by ring
  exact hy (he ▸ hd)

/-- The origin avoids all six zero residues at each prime divisor of `W`. -/
theorem point_zero_avoids_prime (a b c : ℤ) {p : ℕ} (hp : p.Prime) (hw : (p : ℤ) ∣ W)
    (i : Fin 6) : ¬ (p : ℤ) ∣ (point a b c 0 0).coord i := by
  have hwP : W ∣ P ^ 3 := ⟨162813749175, by norm_num [W, P]⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (p : ℤ) ∣ P := hpZ.dvd_of_dvd_pow (dvd_trans hw hwP)
  have hone : ¬ (p : ℤ) ∣ (1 : ℤ) := by
    intro h
    have h' : p ∣ 1 := by simpa using Int.natAbs_dvd_natAbs.mpr h
    exact hp.ne_one (Nat.dvd_one.mp h')
  have hneg : ¬ (p : ℤ) ∣ (-1 : ℤ) := by simpa using hone
  have h3917 : ¬ (p : ℤ) ∣ (3917 : ℤ) := by
    intro h
    have hd : (p : ℤ) ∣ 1369 * P + (-3178537 : ℤ) * 3917 :=
      Int.dvd_add (Int.dvd_mul_of_dvd_right hP) (Int.dvd_mul_of_dvd_right h)
    have he : 1369 * P + (-3178537 : ℤ) * 3917 = 1 := by norm_num [P]
    rw [he] at hd
    exact hone hd
  have h239 : ¬ (p : ℤ) ∣ (239 : ℤ) := by
    intro h
    have hd : (p : ℤ) ∣ 74 * P + (-2815861 : ℤ) * 239 :=
      Int.dvd_add (Int.dvd_mul_of_dvd_right hP) (Int.dvd_mul_of_dvd_right h)
    have he : 74 * P + (-2815861 : ℤ) * 239 = 1 := by norm_num [P]
    rw [he] at hd
    exact hone hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := point_zero_residues a b c
  fin_cases i <;> simp only [Sextuple.coord]
  · exact nondiv_of_residue (dvd_trans hP h1) hneg
  · exact nondiv_of_residue (dvd_trans hP h2) hneg
  · exact nondiv_of_residue (dvd_trans hP h3) h3917
  · exact nondiv_of_residue (dvd_trans hP h4) hneg
  · exact nondiv_of_residue (dvd_trans hP h5) hneg
  · exact nondiv_of_residue (dvd_trans hP h6) h239

private theorem point_p5 (a b c n m : ℤ) :
    (point a b c n m).p5 = -1 - W * b * r n - W * c * s m := rfl

private theorem point_p2 (a b c n m : ℤ) :
    (point a b c n m).p2 = W * a * s m + 462 * W * b * (point a b c n m).p5 +
      (point a b c n m).p5 := rfl

private theorem point_p4 (a b c n m : ℤ) :
    (point a b c n m).p4 = -(W * a * r n) + 462 * W * c * (point a b c n m).p5 +
      (point a b c n m).p5 := rfl

private theorem point_p5_ne_zero (a b c n m : ℤ) : (point a b c n m).p5 ≠ 0 := by
  have h : (point a b c n m).p5 = -1 - 2 * (254 * P * (b * r n + c * s m)) := by
    rw [point_p5, W]
    ring
  omega

private theorem sliced_overlap_equations {a b c a' b' c' n m : ℤ}
    (h : point a b c n m = point a' b' c' n m) :
    (a - a') * s m + 462 * (b - b') * (point a b c n m).p5 = 0 ∧
      (a - a') * r n - 462 * (c - c') * (point a b c n m).p5 = 0 := by
  have h5 := congrArg Sextuple.p5 h
  have h2 := congrArg Sextuple.p2 h
  have h4 := congrArg Sextuple.p4 h
  rw [point_p2, point_p2, ← h5] at h2
  rw [point_p4, point_p4, ← h5] at h4
  have hW : W ≠ 0 := by norm_num [W, P]
  constructor
  · have hmul : W * ((a - a') * s m + 462 * (b - b') * (point a b c n m).p5) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp hmul).resolve_left hW
  · have hmul : W * ((a - a') * r n - 462 * (c - c') * (point a b c n m).p5) = 0 := by
      linear_combination -h4
    exact (mul_eq_zero.mp hmul).resolve_left hW

/-- Distinct parameter triples have at most one shared point on the fixed lattice. -/
theorem distinct_planes_at_most_one {a b c a' b' c' n m n' m' : ℤ}
    (different : (a, b, c) ≠ (a', b', c'))
    (hx : point a b c n m = point a' b' c' n m)
    (hy : point a b c n' m' = point a' b' c' n' m') : (n, m) = (n', m') := by
  obtain ⟨hsx, hrx⟩ := sliced_overlap_equations hx
  obtain ⟨hsy, hry⟩ := sliced_overlap_equations hy
  have ha : a - a' ≠ 0 := by
    intro hz
    have ht := point_p5_ne_zero a b c n m
    have hnum : (462 : ℤ) ≠ 0 := by decide
    have hbmul : 462 * (b - b') * (point a b c n m).p5 = 0 := by
      simpa [hz] using hsx
    have hcmul : 462 * (c - c') * (point a b c n m).p5 = 0 := by
      simpa [hz] using hrx
    have hb : b = b' := sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp hbmul).resolve_right ht)).resolve_left hnum)
    have hc : c = c' := sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp hcmul).resolve_right ht)).resolve_left hnum)
    exact different (by rw [sub_eq_zero.mp hz, hb, hc])
  let k := a - a' + 462 * W * (b * (c - c') - c * (b - b'))
  have hkx : k * (point a b c n m).p5 = -(a - a') := by
    dsimp only [k]
    linear_combination (a - a') * (point_p5 a b c n m) - (W * b) * hrx - (W * c) * hsx
  have hky : k * (point a b c n' m').p5 = -(a - a') := by
    dsimp only [k]
    linear_combination (a - a') * (point_p5 a b c n' m') - (W * b) * hry - (W * c) * hsy
  have hk : k ≠ 0 := by
    intro hzero
    have hneg : -(a - a') = 0 := by simpa [hzero] using hkx.symm
    exact ha (neg_eq_zero.mp hneg)
  have h5 := mul_left_cancel₀ hk (hkx.trans hky.symm)
  apply Prod.ext
  · have hr : (a - a') * r n = (a - a') * r n' := by
      linear_combination hrx - hry + (462 * (c - c')) * h5
    have h := mul_left_cancel₀ ha hr
    unfold r at h
    change n = n'
    omega
  · have hs : (a - a') * s m = (a - a') * s m' := by
      linear_combination hsx - hsy - (462 * (b - b')) * h5
    have h := mul_left_cancel₀ ha hs
    unfold s at h
    change m = m'
    omega

end Jsp000881.Plane
