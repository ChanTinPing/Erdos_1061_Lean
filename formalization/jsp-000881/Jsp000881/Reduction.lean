module

public import Jsp000881.Plane
import all Jsp000881.Plane
public import Jsp000881.Solutions
import all Jsp000881.Solutions
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

public section

namespace Jsp000881

open Filter Asymptotics
open scoped ArithmeticFunction.sigma Topology

noncomputable def solutionsBelow (x : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 ⌊x⌋₊).product (Finset.Icc 1 ⌊x⌋₊)).filter fun (a, b) =>
    (↑(a + b) : ℝ) ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)

/-- The counting function of `FormalConjectures/ErdosProblems/1061.lean`. -/
noncomputable abbrev S (x : ℝ) : ℝ := (solutionsBelow x).card

def Plane.Sextuple.toPrimes (p : Plane.Sextuple) : PrimeTuple :=
  ⟨p.p1.toNat, p.p2.toNat, p.p3.toNat, p.p4.toNat, p.p5.toNat, p.p6.toNat⟩

def Plane.Sextuple.CoordinatesNonnegative (p : Plane.Sextuple) : Prop :=
  0 ≤ p.p1 ∧ 0 ≤ p.p2 ∧ 0 ≤ p.p3 ∧ 0 ≤ p.p4 ∧ 0 ≤ p.p5 ∧ 0 ≤ p.p6

theorem Plane.point_toPrimes_equations (a b c n m : ℤ)
    (h : (Plane.point a b c n m).CoordinatesNonnegative) :
    (Plane.point a b c n m).toPrimes.LiEquations := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  let s := (Plane.point a b c n m).toPrimes
  change s.LiEquations
  have hp :
      15 * (s.p1 : ℤ) * (s.p2 : ℤ) + 31 * (s.p3 : ℤ) * (s.p4 : ℤ) =
        508 * (s.p5 : ℤ) * (s.p6 : ℤ) := by
    simpa only [s, Plane.Sextuple.toPrimes, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2,
      Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h5,
      Int.toNat_of_nonneg h6] using Plane.point_product a b c n m
  have hs :
      15 * ((s.p1 : ℤ) + (s.p2 : ℤ)) + 31 * ((s.p3 : ℤ) + (s.p4 : ℤ)) =
        508 * ((s.p5 : ℤ) + (s.p6 : ℤ)) + 462 := by
    simpa only [s, Plane.Sextuple.toPrimes, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2,
      Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4, Int.toNat_of_nonneg h5,
      Int.toNat_of_nonneg h6] using Plane.point_sum a b c n m
  constructor
  · exact_mod_cast hp
  · exact_mod_cast hs

/-- Distinct tuples are counted only once, even when realized on two planes. -/
def PrimeTuple.IsRealizedBelow (s : PrimeTuple) (x : ℝ) : Prop :=
  s.IsOrderedFresh ∧ (↑(1828800 * s.p5 * s.p6 : ℕ) : ℝ) ≤ x ∧
    ∃ a b c n m : ℤ, (Plane.point a b c n m).CoordinatesNonnegative ∧
      (Plane.point a b c n m).toPrimes = s

theorem realized_equations {s : PrimeTuple} {x : ℝ} (h : s.IsRealizedBelow x) : s.LiEquations := by
  obtain ⟨a, b, c, n, m, hn, hs⟩ := h.2.2
  rw [← hs]
  exact Plane.point_toPrimes_equations a b c n m hn

theorem solution_mem_of_realized {s : PrimeTuple} {x : ℝ} (h : s.IsRealizedBelow x) :
    s.solution ∈ solutionsBelow x := by
  classical
  have he := realized_equations h
  obtain ⟨ha, hb⟩ := PrimeTuple.solution_positive h.1
  have hper := h.2.1
  rw [← PrimeTuple.solution_perimeter he] at hper
  have ha' : (s.solution.1 : ℝ) ≤ x := by
    push_cast at hper
    have : (0 : ℝ) ≤ (s.solution.2 : ℝ) := Nat.cast_nonneg _
    linarith only [hper, this]
  have hb' : (s.solution.2 : ℝ) ≤ x := by
    push_cast at hper
    have : (0 : ℝ) ≤ (s.solution.1 : ℝ) := Nat.cast_nonneg _
    linarith only [hper, this]
  unfold solutionsBelow
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨ha, Nat.le_floor ha'⟩, Finset.mem_Icc.mpr ⟨hb, Nat.le_floor hb'⟩⟩,
    hper, PrimeTuple.solution_sigma h.1 he⟩

theorem card_le_count {F : Finset PrimeTuple} {x : ℝ}
    (hF : ∀ s ∈ F, s.IsRealizedBelow x) : (F.card : ℝ) ≤ S x := by
  have hcard : F.card ≤ (solutionsBelow x).card :=
    Finset.card_le_card_of_injOn PrimeTuple.solution
      (fun s hs => solution_mem_of_realized (hF s hs))
      (fun s hs t ht hst => PrimeTuple.solution_injOn
        ⟨(hF s hs).1, realized_equations (hF s hs)⟩
        ⟨(hF t ht).1, realized_equations (hF t ht)⟩ hst)
  exact_mod_cast hcard

/-- The unresolved analytical input is expressed as a lower bound for the
distinct prime tuples realized by the integral planes. -/
def PlaneCountLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
    ∃ F : Finset PrimeTuple, (∀ s ∈ F, s.IsRealizedBelow x) ∧ c * x * Real.log x ≤ F.card

theorem eventually_arbitrary_linear_lower_bound (h : PlaneCountLowerBound) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M * x ≤ S x := by
  obtain ⟨c, hc, hl⟩ := h
  have hlog : ∀ᶠ x : ℝ in atTop, M / c ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (M / c))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlog, hl] with x hxp hxl hxs
  obtain ⟨F, hf, hcard⟩ := hxs
  have hM : M ≤ Real.log x * c := (div_le_iff₀ hc).mp hxl
  calc
    M * x ≤ (Real.log x * c) * x := mul_le_mul_of_nonneg_right hM hxp.le
    _ = c * x * Real.log x := by ring
    _ ≤ F.card := hcard
    _ ≤ S x := card_le_count hf

/-- Full Erdős #1061 conclusion derived from the stated plane-count input. -/
theorem not_linear_asymptotic_of_plane_count (h : PlaneCountLowerBound) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) := by
  rintro ⟨c, hc, he⟩
  have hx : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have hne : ∀ᶠ x : ℝ in atTop, c * x ≠ 0 := hx.mono fun _ hx' => (mul_pos hc hx').ne'
  have hlim := (isEquivalent_iff_tendsto_one hne).mp he
  have hup : ∀ᶠ x : ℝ in atTop, S x / (c * x) < 2 :=
    (tendsto_order.1 hlim).2 2 (by norm_num)
  obtain ⟨x, hxp, hxup, hxlo⟩ := (hx.and (hup.and
    (eventually_arbitrary_linear_lower_bound h (2 * c)))).exists
  have hlt := (div_lt_iff₀ (mul_pos hc hxp)).mp hxup
  exact (not_lt_of_ge hxlo) (by simpa only [mul_assoc] using hlt)

end Jsp000881
