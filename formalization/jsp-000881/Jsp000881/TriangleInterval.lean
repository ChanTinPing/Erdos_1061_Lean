module

public import Jsp000881.TriangleCutoff
import all Jsp000881.TriangleCutoff
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith

public section

namespace Jsp000881

/-- The residues of the integer interval from zero through `M`. -/
def triangleInterval (p M : ℕ) : Finset (ZMod p) :=
  (Finset.range (M + 1)).image fun n : ℕ => (n : ZMod p)

private theorem natCast_mem_triangleInterval {p M n : ℕ} (hn : n ≤ M) :
    (n : ZMod p) ∈ triangleInterval p M :=
  Finset.mem_image_of_mem (fun k : ℕ => (k : ZMod p))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem triangleInterval_nonempty (p M : ℕ) : (triangleInterval p M).Nonempty :=
  ⟨(0 : ℕ), natCast_mem_triangleInterval (Nat.zero_le M)⟩

theorem triangleInterval_card {p M : ℕ} (hp : M < p) : (triangleInterval p M).card = M + 1 := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod p)) (Finset.range (M + 1) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < M + 1 := Finset.mem_range.mp hx
    have hy' : y < M + 1 := Finset.mem_range.mp hy
    have h := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt (by omega : x < p),
      ZMod.val_natCast_of_lt (by omega : y < p)] using h
  rw [triangleInterval, Finset.card_image_of_injOn hinj, Finset.card_range]

open Classical in
private theorem overlap_ratio_le_cutoff {α K : Type*} [Add K] (E : Finset K) (u : K)
    (S : Finset α) (f : α → K) (hf : ∀ i ∈ S, f i ∈ E ∧ f i + u ∈ E)
    (hinj : Set.InjOn f (S : Set α)) :
    (S.card : ℝ) / (E.card : ℝ) ≤ (triangleCutoff E u).re := by
  rw [triangleCutoff_re_eq]
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hc : S.card ≤ (E.filter fun x => x + u ∈ E).card :=
    Finset.card_le_card_of_injOn f (fun i hi => Finset.mem_filter.mpr (hf i hi)) hinj
  exact_mod_cast hc

open Classical in
private theorem exists_overlap_of_cutoff_ne_zero {K : Type*} [Add K] (E : Finset K) (u : K)
    (h : triangleCutoff E u ≠ 0) : ∃ x ∈ E, x + u ∈ E := by
  let F := E.filter fun x => x + u ∈ E
  have hF : F.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    apply h
    unfold triangleCutoff
    change (F.card : ℂ) / (E.card : ℂ) = 0
    rw [he]
    simp
  obtain ⟨x, hx⟩ := hF
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- At every integer shift of absolute value at most half the interval,
at least half the residues contribute to the cutoff. -/
theorem triangleInterval_re_ge_half {p M : ℕ} (hp : M < p) (t : ℤ)
    (ht : 2 * |t| ≤ (M : ℤ)) :
    (1 : ℝ) / 2 ≤ (triangleCutoff (triangleInterval p M) (t : ZMod p)).re := by
  let l := (-t).toNat
  let r := t.toNat
  have hs : (l : ℤ) + t = (r : ℤ) ∧ (l : ℤ) + (r : ℤ) = |t| := by
    dsimp only [l, r]
    by_cases ht0 : 0 ≤ t
    · rw [Int.toNat_of_nonpos (by omega : -t ≤ 0), Int.toNat_of_nonneg ht0, abs_of_nonneg ht0]
      simp
    · have ht1 : t ≤ 0 := by omega
      rw [Int.toNat_of_nonpos ht1, Int.toNat_of_nonneg (by omega : 0 ≤ -t), abs_of_nonpos ht1]
      simp
  have hcast : (l : ZMod p) + (t : ZMod p) = (r : ZMod p) := by
    simpa only [Int.cast_add, Int.cast_natCast] using congrArg (fun v : ℤ => (v : ZMod p)) hs.1
  have hd : 2 * (l + r) ≤ M := by omega
  let S := Finset.range (M + 1 - (l + r))
  let f : ℕ → ZMod p := fun i => ((i + l : ℕ) : ZMod p)
  have hf : ∀ i ∈ S, f i ∈ triangleInterval p M ∧ f i + (t : ZMod p) ∈ triangleInterval p M := by
    intro i hi
    have hi' : i < M + 1 - (l + r) := Finset.mem_range.mp hi
    refine ⟨natCast_mem_triangleInterval (by omega : i + l ≤ M), ?_⟩
    have hfi : f i + (t : ZMod p) = ((i + r : ℕ) : ZMod p) := by
      simp only [f, Nat.cast_add, add_assoc, hcast]
    rw [hfi]
    exact natCast_mem_triangleInterval (by omega : i + r ≤ M)
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < M + 1 - (l + r) := Finset.mem_range.mp hi
    have hj' : j < M + 1 - (l + r) := Finset.mem_range.mp hj
    have hval := congrArg ZMod.val hij
    change ((i + l : ℕ) : ZMod p).val = ((j + l : ℕ) : ZMod p).val at hval
    rw [ZMod.val_natCast_of_lt (by omega : i + l < p),
      ZMod.val_natCast_of_lt (by omega : j + l < p)] at hval
    omega
  have hhalf : M + 1 ≤ 2 * S.card := by
    simp only [S, Finset.card_range]
    omega
  have hhalf' : (M : ℝ) + 1 ≤ 2 * (S.card : ℝ) := by
    exact_mod_cast hhalf
  refine le_trans ?_ (overlap_ratio_le_cutoff (triangleInterval p M) (t : ZMod p) S f hf hinj)
  rw [triangleInterval_card hp]
  apply (le_div_iff₀ (by positivity)).mpr
  push_cast
  linarith only [hhalf']

theorem triangleInterval_translate_re_ge_half {p M : ℕ} (hp : M < p) (c : ZMod p) (t : ℤ)
    (ht : 2 * |t| ≤ (M : ℤ)) :
    (1 : ℝ) / 2 ≤ (triangleCutoff (triangleInterval p M) (c + (t : ZMod p) - c)).re := by
  rw [show c + (t : ZMod p) - c = (t : ZMod p) by ring]
  exact triangleInterval_re_ge_half hp t ht

/-- A translated cutoff can be nonzero only at a translate of an integer
whose absolute value is at most the interval length minus one. -/
theorem triangleInterval_translate_support {p M : ℕ} {c z : ZMod p}
    (h : triangleCutoff (triangleInterval p M) (z - c) ≠ 0) :
    ∃ t : ℤ, |t| ≤ (M : ℤ) ∧ z = c + (t : ZMod p) := by
  obtain ⟨u, hu, hu'⟩ := exists_overlap_of_cutoff_ne_zero _ _ h
  obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hu'
  have hx' := Finset.mem_range.mp hx
  have hy' := Finset.mem_range.mp hy
  refine ⟨(y : ℤ) - (x : ℤ), ?_, ?_⟩
  · exact abs_le.mpr ⟨by omega, by omega⟩
  · simp only [Int.cast_sub, Int.cast_natCast, hxu, hyu]
    ring

/-- With no wraparound, nonzero weight on an integer representative forces
the representative itself to lie in the centered interval. -/
theorem triangleInterval_translate_int_support {p M : ℕ} {c x : ℤ}
    (hp : |x - c| + (M : ℤ) < (p : ℤ))
    (h : triangleCutoff (triangleInterval p M) ((x : ZMod p) - (c : ZMod p)) ≠ 0) :
    |x - c| ≤ (M : ℤ) := by
  obtain ⟨t, ht, heq⟩ := triangleInterval_translate_support h
  have hdvd : (p : ℤ) ∣ x - c - t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, Int.cast_sub, heq]
    ring
  have hbound : |x - c - t| < (p : ℤ) :=
    ((abs_sub _ _).trans (Int.add_le_add_left ht _)).trans_lt hp
  have hzero : x - c - t = 0 := by
    by_contra hn
    exact (not_lt_of_ge (Int.le_abs_of_dvd hn hdvd)) hbound
  rw [sub_eq_zero.mp hzero]
  exact ht

end Jsp000881
