module

public import Jsp000881.Rectangles
import all Jsp000881.Rectangles
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.IntervalCases

/-!
# Local degeneracy of the six integral forms

Use the coordinates `r = 15 y₁` and `s = 31 y₃` from the integral lattice.
The first, third, and sixth forms are scaled by `15`, `31`, and `508`
respectively to keep all coefficients integral.
-/

public section

namespace Jsp000881.Plane

structure AffineRow (R : Type*) where
  constant : R
  left : R
  right : R

def AffineRow.eval {R : Type*} [Semiring R] (row : AffineRow R) (r s : R) : R :=
  row.constant + row.left * r + row.right * s

theorem AffineRow.identically_zero_iff {R : Type*} [Semiring R] (row : AffineRow R) :
    (∀ r s, row.eval r s = 0) ↔ row.constant = 0 ∧ row.left = 0 ∧ row.right = 0 := by
  constructor
  · intro h
    have hc : row.constant = 0 := by simpa [AffineRow.eval] using h 0 0
    exact ⟨hc, by simpa [AffineRow.eval, hc] using h 1 0,
      by simpa [AffineRow.eval, hc] using h 0 1⟩
  · rintro ⟨hc, hl, hr⟩ r s
    simp [AffineRow.eval, hc, hl, hr]

/-- The negated constant of the scaled sixth form. -/
def obstruction {R : Type*} [Ring R] (β γ : R) : R := 462 * (15 * β + 31 * γ) + 46

def coordinateScale (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 15
  | 2 => 31
  | 5 => 508
  | _ => 1

/-- Affine coefficient rows for the scaled coordinates in `(r,s)`. -/
def coordinateRow {R : Type*} [Ring R] (α β γ : R) (i : Fin 6) : AffineRow R :=
  let B := 462 * β + 1
  let C := 462 * γ + 1
  let E := obstruction β γ
  match i.val with
  | 0 => ⟨-15, 1 - 15 * β, -15 * γ⟩
  | 1 => ⟨-B, -B * β, α - B * γ⟩
  | 2 => ⟨-31, -31 * β, 1 - 31 * γ⟩
  | 3 => ⟨-C, -α - C * β, -C * γ⟩
  | 4 => ⟨-1, -β, -γ⟩
  | _ => ⟨-E, -β * E - (31 * α - 462 * β - 1), -γ * E + 15 * α + 462 * γ + 1⟩

def latticeR (n : ℤ) : ℤ := 15 * (508 * n)

def latticeS (m : ℤ) : ℤ := 31 * (3918 + 508 * m)

private def latticeT (b c n m : ℤ) : ℤ := -1 - W * b * latticeR n - W * c * latticeS m

private theorem point_formulas (a b c n m : ℤ) :
    (point a b c n m).p1 = 508 * n + latticeT b c n m ∧
    (point a b c n m).p2 = W * a * latticeS m + (462 * W * b + 1) * latticeT b c n m ∧
    (point a b c n m).p3 = 3918 + 508 * m + latticeT b c n m ∧
    (point a b c n m).p4 = -(W * a * latticeR n) + (462 * W * c + 1) * latticeT b c n m ∧
    (point a b c n m).p5 = latticeT b c n m := by
  refine ⟨rfl, ?_, rfl, ?_, rfl⟩
  · change W * a * latticeS m + 462 * W * b * latticeT b c n m + latticeT b c n m = _
    ring
  · change -(W * a * latticeR n) + 462 * W * c * latticeT b c n m + latticeT b c n m = _
    ring

theorem scaled_point_eq_row (a b c n m : ℤ) (i : Fin 6) :
    coordinateScale i * (point a b c n m).coord i =
      (coordinateRow (W * a) (W * b) (W * c) i).eval (latticeR n) (latticeS m) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := point_formulas a b c n m
  fin_cases i <;> simp only [coordinateScale, Sextuple.coord, coordinateRow, AffineRow.eval]
  all_goals
    simp only [point_sixth, h1, h2, h3, h4, h5, latticeT, latticeR, latticeS, obstruction, one_mul]
    ring

theorem scaled_point_eq_row_mod (p : ℕ) (a b c n m : ℤ) (i : Fin 6) :
    (coordinateScale i : ZMod p) * ((point a b c n m).coord i : ZMod p) =
      (coordinateRow ((W * a : ℤ) : ZMod p) ((W * b : ℤ) : ZMod p)
        ((W * c : ℤ) : ZMod p) i).eval
        (latticeR n : ZMod p) (latticeS m : ZMod p) := by
  have h := congrArg (fun x : ℤ => (x : ZMod p)) (scaled_point_eq_row a b c n m i)
  fin_cases i <;> simp only [coordinateRow, AffineRow.eval, obstruction] at h ⊢ <;>
    push_cast at h ⊢ <;> exact h

/-- The three possible bad congruence conditions in the parameter sieve. -/
def DegenerateResidue {R : Type*} [Ring R] (α β γ : R) (i : Fin 6) : Prop :=
  match i.val with
  | 1 => 462 * β + 1 = 0 ∧ α = 0
  | 3 => 462 * γ + 1 = 0 ∧ α = 0
  | 5 => obstruction β γ = 0 ∧ 31 * α = 462 * β + 1
  | _ => False

private theorem cast_ne_zero_of_dvd_W {p : ℕ} {d : ℤ} (hd : d ∣ W)
    (hw : (W : ZMod p) ≠ 0) : (d : ZMod p) ≠ 0 := by
  intro h
  exact hw ((ZMod.intCast_zmod_eq_zero_iff_dvd W p).mpr
    (dvd_trans ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h) hd))

theorem coordinateScale_ne_zero_mod {p : ℕ} (hw : (W : ZMod p) ≠ 0) (i : Fin 6) :
    (coordinateScale i : ZMod p) ≠ 0 := by
  apply cast_ne_zero_of_dvd_W _ hw
  fin_cases i <;> decide

/-- Over a prime field away from `W`, exactly three rows can vanish identically. -/
theorem row_degenerate_iff {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (α β γ : ZMod p) (i : Fin 6) :
    (∀ r s, (coordinateRow α β γ i).eval r s = 0) ↔ DegenerateResidue α β γ i := by
  have h15 : (15 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 15) (by decide) hw
  have h31 : (31 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 31) (by decide) hw
  rw [AffineRow.identically_zero_iff]
  fin_cases i <;> simp only [coordinateRow, DegenerateResidue]
  · simp [h15]
  · constructor
    · rintro ⟨h, _, hr⟩
      have hb := neg_eq_zero.mp h
      exact ⟨hb, by simpa [hb] using hr⟩
    · rintro ⟨hb, ha⟩
      simp [hb, ha]
  · simp [h31]
  · constructor
    · rintro ⟨h, hl, _⟩
      have hc := neg_eq_zero.mp h
      exact ⟨hc, by simpa [hc] using hl⟩
    · rintro ⟨hc, ha⟩
      simp [hc, ha]
  · simp
  · have hrel : 31 * (15 * α + 462 * γ + 1) - 15 * (31 * α - 462 * β - 1) =
      obstruction β γ := by
      unfold obstruction
      ring
    constructor
    · rintro ⟨h, hl, _⟩
      have he := neg_eq_zero.mp h
      exact ⟨he, by linear_combination -hl - β * he⟩
    · rintro ⟨he, ha⟩
      have hdiff : 31 * α - 462 * β - 1 = 0 := by linear_combination ha
      have hprod : 31 * (15 * α + 462 * γ + 1) = 0 := by simpa [he, hdiff] using hrel
      have hr := (mul_eq_zero.mp hprod).resolve_left h31
      simp [he, hdiff, hr]

/-- Every pair of transformed residues comes from the fixed lattice away from `W`. -/
theorem exists_lattice_indices_mod {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (r s : ZMod p) : ∃ n m : ℤ, (latticeR n : ZMod p) = r ∧ (latticeS m : ZMod p) = s := by
  have h15 : (15 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 15) (by decide) hw
  have h31 : (31 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 31) (by decide) hw
  have h508 : (508 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 508) (by decide) hw
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (r / (15 * 508))
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective ((s - 31 * 3918) / (31 * 508))
  refine ⟨n, m, ?_, ?_⟩
  · simp only [latticeR, Int.cast_mul, Int.cast_ofNat, hn]
    calc
      _ = (15 * 508) * (r / (15 * 508)) := by ring
      _ = r := mul_div_cancel₀ r (mul_ne_zero h15 h508)
  · simp only [latticeS, Int.cast_mul, Int.cast_add, Int.cast_ofNat, hm]
    calc
      _ = 31 * 3918 + (31 * 508) * ((s - 31 * 3918) / (31 * 508)) := by ring
      _ = 31 * 3918 + (s - 31 * 3918) := by rw [mul_div_cancel₀ _ (mul_ne_zero h31 h508)]
      _ = s := by ring

/-- The residue tests for the original lattice evaluations of the six coordinates. -/
theorem point_degenerate_iff {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (a b c : ℤ) (i : Fin 6) :
    (∀ n m : ℤ, (p : ℤ) ∣ (point a b c n m).coord i) ↔
      DegenerateResidue ((W * a : ℤ) : ZMod p) ((W * b : ℤ) : ZMod p)
        ((W * c : ℤ) : ZMod p) i := by
  rw [← row_degenerate_iff hw]
  constructor
  · intro h r s
    obtain ⟨n, m, hr, hs⟩ := exists_lattice_indices_mod hw r s
    rw [← hr, ← hs, ← scaled_point_eq_row_mod, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (h n m),
      mul_zero]
  · intro h n m
    have hz := h (latticeR n : ZMod p) (latticeS m : ZMod p)
    rw [← scaled_point_eq_row_mod] at hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      ((mul_eq_zero.mp hz).resolve_left (coordinateScale_ne_zero_mod hw i))

noncomputable def AffineRow.zeros {K : Type*} [Field K] [Fintype K]
    (row : AffineRow K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter fun rs => row.eval rs.1 rs.2 = 0

private theorem AffineRow.mem_zeros {K : Type*} [Field K] [Fintype K]
    (row : AffineRow K) (rs : K × K) : rs ∈ row.zeros ↔ row.eval rs.1 rs.2 = 0 := by
  classical
  simp [AffineRow.zeros]

theorem AffineRow.card_zeros_le {K : Type*} [Field K] [Fintype K] (row : AffineRow K)
    (h : ¬ ∀ r s, row.eval r s = 0) : row.zeros.card ≤ Fintype.card K := by
  classical
  change row.zeros.card ≤ (Finset.univ : Finset K).card
  by_cases hr : row.right = 0
  · by_cases hl : row.left = 0
    · have hc : row.constant ≠ 0 := by
        intro hz
        exact h ((row.identically_zero_iff).mpr ⟨hz, hl, hr⟩)
      have hz : row.zeros = ∅ := by
        ext rs
        simp [row.mem_zeros, AffineRow.eval, hr, hl, hc]
      simp [hz]
    · refine Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) ?_
      intro x hx y hy hxy
      have hx' := (row.mem_zeros x).mp hx
      have hy' := (row.mem_zeros y).mp hy
      simp only [AffineRow.eval, hr, zero_mul, add_zero] at hx' hy'
      have hp : row.left * (x.1 - y.1) = 0 := by linear_combination hx' - hy'
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hl)) hxy
  · refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_univ _) ?_
    intro x hx y hy hxy
    change x.1 = y.1 at hxy
    have hx' := (row.mem_zeros x).mp hx
    have hy' := (row.mem_zeros y).mp hy
    simp only [AffineRow.eval, hxy] at hx' hy'
    have hp : row.right * (x.2 - y.2) = 0 := by linear_combination hx' - hy'
    exact Prod.ext hxy (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hr))

theorem prime_twelve_lt_of_W_ne_zero {p : ℕ} (hp : p.Prime) (hw : (W : ZMod p) ≠ 0) :
    12 < p := by
  by_contra h
  have hle : p ≤ 12 := by omega
  have hp2 := hp.two_le
  interval_cases p <;> first
    | exact hw ((ZMod.intCast_zmod_eq_zero_iff_dvd W _).mpr (by decide))
    | exact (by decide : ¬ Nat.Prime 9) hp

noncomputable def goodResiduePairs {p : ℕ} [Fact p.Prime] (α β γ : ZMod p) :
    Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter fun rs => ∀ i, (coordinateRow α β γ i).eval rs.1 rs.2 ≠ 0

/-- Away from `W`, the union of the six zero sets has at most `6 * p` points. -/
theorem card_goodResiduePairs_ge {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (α β γ : ZMod p) (hgood : ∀ i, ¬ DegenerateResidue α β γ i) :
    p * p - 6 * p ≤ (goodResiduePairs α β γ).card := by
  classical
  let zeros := fun i : Fin 6 => (coordinateRow α β γ i).zeros
  let bad := (Finset.univ : Finset (Fin 6)).biUnion zeros
  have hcard : bad.card ≤ 6 * p := by
    have hb := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 6)) zeros p
      (fun i _ => ((coordinateRow α β γ i).card_zeros_le
        (mt (row_degenerate_iff hw α β γ i).mp (hgood i))).trans_eq (ZMod.card p))
    simpa [bad] using hb
  have hmem (rs : ZMod p × ZMod p) : rs ∈ bad ↔
      ∃ i, (coordinateRow α β γ i).eval rs.1 rs.2 = 0 := by
    simp only [bad, zeros, Finset.mem_biUnion, Finset.mem_univ, true_and, AffineRow.mem_zeros]
  have he : goodResiduePairs α β γ = Finset.univ \ bad := by
    ext rs
    simp only [goodResiduePairs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hmem]
    exact ⟨fun h ⟨i, hi⟩ => h i hi, fun h i hi => h ⟨i, hi⟩⟩
  rw [he, Finset.card_univ_sdiff, Fintype.card_prod, ZMod.card p]
  exact Nat.sub_le_sub_left hcard _

theorem exists_row_modular_witness {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (α β γ : ZMod p) (hgood : ∀ i, ¬ DegenerateResidue α β γ i) :
    ∃ r s, ∀ i, (coordinateRow α β γ i).eval r s ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hp6 : 6 < p := lt_trans (by decide) (prime_twelve_lt_of_W_ne_zero hp hw)
  have hpos := Nat.sub_pos_of_lt (Nat.mul_lt_mul_of_pos_right hp6 hp.pos)
  obtain ⟨rs, hrs⟩ := Finset.card_pos.mp (hpos.trans_le (card_goodResiduePairs_ge hw α β γ hgood))
  exact ⟨rs.1, rs.2, (Finset.mem_filter.mp hrs).2⟩

/-- The residue tests suffice for a point where no coordinate is divisible by `p`. -/
theorem exists_point_modular_witness {p : ℕ} [Fact p.Prime] (a b c : ℤ)
    (hgood : (W : ZMod p) ≠ 0 → ∀ i, ¬ DegenerateResidue
      ((W * a : ℤ) : ZMod p) ((W * b : ℤ) : ZMod p) ((W * c : ℤ) : ZMod p) i) :
    ∃ n m : ℤ, ∀ i, ¬ (p : ℤ) ∣ (point a b c n m).coord i := by
  by_cases hw : (W : ZMod p) = 0
  · exact ⟨0, 0, point_zero_avoids_prime a b c Fact.out
      ((ZMod.intCast_zmod_eq_zero_iff_dvd W p).mp hw)⟩
  · obtain ⟨r, s, h⟩ := exists_row_modular_witness hw _ _ _ (hgood hw)
    obtain ⟨n, m, hn, hm⟩ := exists_lattice_indices_mod hw r s
    refine ⟨n, m, fun i hd => h i ?_⟩
    rw [← hn, ← hm, ← scaled_point_eq_row_mod, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd,
      mul_zero]

def BadParameterResidue (p : ℕ) (θ : PlaneIndex) (i : Fin 6) : Prop :=
  DegenerateResidue ((W * θ.1 : ℤ) : ZMod p) ((W * θ.2.1 : ℤ) : ZMod p)
    ((W * θ.2.2 : ℤ) : ZMod p) i

theorem locallyAdmissible_of_not_badParameterResidue (θ : PlaneIndex)
    (h : ∀ p : ℕ, p.Prime → (W : ZMod p) ≠ 0 → ∀ i, ¬ BadParameterResidue p θ i) :
    LocallyAdmissible θ := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, m, hn⟩ := exists_point_modular_witness (p := p) θ.1 θ.2.1 θ.2.2 (h p hp)
  exact ⟨(n, m), hn⟩

theorem parameter_bad_prime_le {p : ℕ} {θ : PlaneIndex} {z : ℤ} (hz : 1 ≤ z)
    (hθ : ParameterBox θ z) (i : Fin 6) (hbad : BadParameterResidue p θ i) :
    (p : ℤ) ≤ 42550 * z := by
  obtain ⟨_, _, hb, hb', hc, hc'⟩ := hθ
  have hle {x : ℤ} (hx : 0 < x) (hd : (x : ZMod p) = 0) : (p : ℤ) ≤ x :=
    Int.le_of_dvd hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hd)
  fin_cases i <;> simp only [BadParameterResidue, DegenerateResidue] at hbad
  all_goals try contradiction
  · have hx : 0 < 462 * (W * θ.2.1) + 1 := by omega
    have hd : ((462 * (W * θ.2.1) + 1 : ℤ) : ZMod p) = 0 := by
      push_cast at hbad ⊢
      exact hbad.1
    exact (hle hx hd).trans (by omega)
  · have hx : 0 < 462 * (W * θ.2.2) + 1 := by omega
    have hd : ((462 * (W * θ.2.2) + 1 : ℤ) : ZMod p) = 0 := by
      push_cast at hbad ⊢
      exact hbad.1
    exact (hle hx hd).trans (by omega)
  · have hx : 0 < obstruction (W * θ.2.1) (W * θ.2.2) := by
      unfold obstruction
      omega
    have hd : ((obstruction (W * θ.2.1) (W * θ.2.2) : ℤ) : ZMod p) = 0 := by
      simp only [obstruction, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hbad ⊢
      exact hbad.1
    refine (hle hx hd).trans ?_
    unfold obstruction
    omega

private theorem first_parameter_residues {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0)
    (a d : ℤ) :
    (462 * ((W * d : ℤ) : ZMod p) + 1 = 0 ∧ ((W * a : ℤ) : ZMod p) = 0) ↔
      (a : ZMod p) = 0 ∧ (d : ZMod p) = -1 / (462 * (W : ZMod p)) := by
  have h462 : (462 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 462) (by decide) hw
  push_cast
  rw [eq_div_iff (mul_ne_zero h462 hw), mul_eq_zero]
  constructor
  · rintro ⟨hd, ha⟩
    exact ⟨ha.resolve_left hw, by linear_combination hd⟩
  · rintro ⟨ha, hd⟩
    exact ⟨by linear_combination hd, Or.inr ha⟩

theorem parameter_residues_x2 {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0) (θ : PlaneIndex) :
    BadParameterResidue p θ 1 ↔
      (θ.1 : ZMod p) = 0 ∧ (θ.2.1 : ZMod p) = -1 / (462 * (W : ZMod p)) :=
  first_parameter_residues hw θ.1 θ.2.1

theorem parameter_residues_x4 {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0) (θ : PlaneIndex) :
    BadParameterResidue p θ 3 ↔
      (θ.1 : ZMod p) = 0 ∧ (θ.2.2 : ZMod p) = -1 / (462 * (W : ZMod p)) :=
  first_parameter_residues hw θ.1 θ.2.2

theorem parameter_residues_x6 {p : ℕ} [Fact p.Prime] (hw : (W : ZMod p) ≠ 0) (θ : PlaneIndex) :
    BadParameterResidue p θ 5 ↔
      (θ.1 : ZMod p) = (462 * (W : ZMod p) * (θ.2.1 : ZMod p) + 1) / (31 * (W : ZMod p)) ∧
      (θ.2.2 : ZMod p) = -(462 * 15 * (W : ZMod p) * (θ.2.1 : ZMod p) + 46) /
        (462 * 31 * (W : ZMod p)) := by
  have h462 : (462 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 462) (by decide) hw
  have h31 : (31 : ZMod p) ≠ 0 := by
    simpa using cast_ne_zero_of_dvd_W (d := 31) (by decide) hw
  simp only [BadParameterResidue, DegenerateResidue, obstruction, Int.cast_mul]
  rw [eq_div_iff (mul_ne_zero h31 hw), eq_div_iff (mul_ne_zero (mul_ne_zero h462 h31) hw)]
  constructor
  · rintro ⟨he, ha⟩
    exact ⟨by linear_combination ha, by linear_combination he⟩
  · rintro ⟨ha, he⟩
    exact ⟨by linear_combination he, by linear_combination ha⟩

end Jsp000881.Plane
