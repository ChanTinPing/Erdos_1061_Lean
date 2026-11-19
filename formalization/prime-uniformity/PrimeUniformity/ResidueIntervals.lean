module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

def interval (start len : ℤ) : Finset ℤ := Finset.Ico start (start + len)

theorem card_interval (start len : ℤ) (h : 0 ≤ len) :
    ((interval start len).card : ℝ) = (len : ℝ) := by
  have hcard : ((interval start len).card : ℤ) = len := by
    unfold interval
    rw [Int.card_Ico_of_le start (start + len) (by omega)]
    omega
  exact_mod_cast hcard

noncomputable def residueSlice (start len : ℤ) {p : ℕ} (r : ZMod p) : Finset ℤ :=
  (interval start len).filter fun n => (n : ZMod p) = r

/-- In an interval of length `L`, each residue class mod `p` contains
at most `L/p+1` integers. -/
theorem card_residueSlice_le (start len : ℤ) {p : ℕ} (hp : 0 < p)
    (hl : 0 ≤ len) (r : ZMod p) :
    ((residueSlice start len r).card : ℝ) ≤ (len : ℝ) / (p : ℝ) + 1 := by
  classical
  let D : ℤ := len / (p : ℤ)
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hD : 0 ≤ D := Int.ediv_nonneg hl hpz.le
  have hcard : (residueSlice start len r).card ≤ (Finset.Icc (0 : ℤ) D).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℤ => (n - start) / (p : ℤ))
    · intro n hn
      change n ∈ residueSlice start len r at hn
      have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_Icc.mpr
        ⟨Int.ediv_nonneg (by omega) hpz.le, Int.ediv_le_ediv hpz (by omega)⟩
    · intro n hn m hm he
      change n ∈ residueSlice start len r at hn
      change m ∈ residueSlice start len r at hm
      have hnm := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
      have hmod := (ZMod.intCast_eq_intCast_iff' n m p).mp hnm
      have hmod' := (Int.emod_sub_cancel_right start).mpr hmod
      have hnEq := Int.mul_ediv_add_emod (n - start) (p : ℤ)
      have hmEq := Int.mul_ediv_add_emod (m - start) (p : ℤ)
      change (n - start) / (p : ℤ) = (m - start) / (p : ℤ) at he
      rw [he, hmod'] at hnEq
      omega
  have hcast : ((Finset.Icc (0 : ℤ) D).card : ℝ) = (D : ℝ) + 1 := by
    have h : ((Finset.Icc (0 : ℤ) D).card : ℤ) = D + 1 := by
      simpa using Int.card_Icc_of_le 0 D (by omega)
    exact_mod_cast h
  have hdiv : (D : ℝ) ≤ (len : ℝ) / (p : ℝ) := by
    apply (le_div_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
    exact_mod_cast (Int.ediv_mul_le len hpz.ne')
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) D).card : ℝ) := by exact_mod_cast hcard
    _ = _ := hcast
    _ ≤ _ := by linarith only [hdiv]

/-- A fixed residue class has discrepancy at most one in an integer interval. -/
theorem residueSlice_discrepancy (start len : ℤ) {p : ℕ} (hp : 0 < p)
    (hl : 0 ≤ len) (r : ZMod p) :
    |((residueSlice start len r).card : ℝ) - (len : ℝ) / (p : ℝ)| ≤ 1 := by
  obtain ⟨v, rfl⟩ := ZMod.intCast_surjective r
  have hmod : residueSlice start len (v : ZMod p) =
      (Finset.Ico start (start + len)).filter fun n => n ≡ v [ZMOD (p : ℤ)] := by
    ext n
    simp [residueSlice, interval, ZMod.intCast_eq_intCast_iff]
  let a : ℚ := ((start : ℚ) - (v : ℚ)) / (p : ℚ)
  let b : ℚ := ((start : ℚ) + (len : ℚ) - (v : ℚ)) / (p : ℚ)
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hlq : (0 : ℚ) ≤ (len : ℚ) := by exact_mod_cast hl
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right (by linarith) hpq.le
  have hd : 0 ≤ ⌈b⌉ - ⌈a⌉ := sub_nonneg.mpr (Int.ceil_mono hab)
  have hcard : ((residueSlice start len (v : ZMod p)).card : ℤ) = ⌈b⌉ - ⌈a⌉ := by
    rw [hmod]
    convert Int.Ico_filter_modEq_card start (start + len) hpz v using 1
    try push_cast
    change ⌈b⌉ - ⌈a⌉ = max (⌈b⌉ - ⌈a⌉) 0
    exact (max_eq_left hd).symm
  have hcardq : ((residueSlice start len (v : ZMod p)).card : ℚ) = (⌈b⌉ : ℚ) - (⌈a⌉ : ℚ) :=
    by exact_mod_cast hcard
  have hlen : (len : ℚ) / (p : ℚ) = b - a := by
    dsimp [a, b]
    rw [← sub_div]
    ring
  have habs : |((residueSlice start len (v : ZMod p)).card : ℚ) - (len : ℚ) / (p : ℚ)| ≤ 1 := by
    rw [hcardq, hlen, abs_le]
    constructor <;> linarith only [Int.le_ceil a, Int.le_ceil b, Int.ceil_lt_add_one a, Int.ceil_lt_add_one b]
  exact_mod_cast habs


end PrimeUniformity
