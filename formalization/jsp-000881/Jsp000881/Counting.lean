module

public import Jsp000881.Reduction
import all Jsp000881.Reduction
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace Jsp000881

open Filter Asymptotics
open scoped BigOperators Topology

/-- A union loses at most (k^2) incidences if each pair of its (k) members
intersects in at most one point. -/
theorem sum_card_le_card_biUnion_add_sq {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α)
    (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ((F i) ∩ (F j)).card ≤ 1) :
    (∑ i ∈ I, (F i).card) ≤ (I.biUnion F).card + I.card ^ 2 := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hsub : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ((F a) ∩ (F b)).card ≤ 1 :=
      fun a ha b hb hab => h a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb) hab
    have hinter : ((F i) ∩ (I.biUnion F)).card ≤ I.card := by
      have hcover : (F i) ∩ (I.biUnion F) ⊆ I.biUnion (fun j => F i ∩ F j) := by
        intro a ha
        obtain ⟨hai, haU⟩ := Finset.mem_inter.mp ha
        obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp haU
        exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hai, haj⟩⟩
      refine (Finset.card_le_card hcover).trans ?_
      simpa using Finset.card_biUnion_le_card_mul I (fun j => F i ∩ F j) 1
        (fun j hj => h i (Finset.mem_insert_self i I) j
          (Finset.mem_insert_of_mem hj) (fun he => hi (he.symm ▸ hj)))
    have hstep := Finset.card_union_add_card_inter (F i) (I.biUnion F)
    have hsq : I.card ^ 2 + I.card ≤ (I.card + 1) ^ 2 := by
      rw [add_sq, mul_one, one_pow]
      omega
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
    have hsum := ih hsub
    omega

/-- Plane parameters are the integer multiples of the fixed modulus in the
three ruling coordinates. -/
abbrev PlaneIndex := ℤ × ℤ × ℤ

def sextupleOn (θ : PlaneIndex) (nm : ℤ × ℤ) : Plane.Sextuple :=
  Plane.point θ.1 θ.2.1 θ.2.2 nm.1 nm.2

/-- The ordered prime tuple comes from a point of this particular plane.
Coordinates are nonnegative so the integer-to-natural conversion is injective. -/
def ComesFrom (θ : PlaneIndex) (s : PrimeTuple) : Prop :=
  ∃ nm : ℤ × ℤ, (sextupleOn θ nm).CoordinatesNonnegative ∧ (sextupleOn θ nm).toPrimes = s

theorem toPrimes_inj {u v : Plane.Sextuple}
    (hu : u.CoordinatesNonnegative) (hv : v.CoordinatesNonnegative)
    (he : u.toPrimes = v.toPrimes) : u = v := by
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ := hv
  have h1 := congrArg (fun s : PrimeTuple => (s.p1 : ℤ)) he
  have h2 := congrArg (fun s : PrimeTuple => (s.p2 : ℤ)) he
  have h3 := congrArg (fun s : PrimeTuple => (s.p3 : ℤ)) he
  have h4 := congrArg (fun s : PrimeTuple => (s.p4 : ℤ)) he
  have h5 := congrArg (fun s : PrimeTuple => (s.p5 : ℤ)) he
  have h6 := congrArg (fun s : PrimeTuple => (s.p6 : ℤ)) he
  simp only [Plane.Sextuple.toPrimes, Int.toNat_of_nonneg hu1, Int.toNat_of_nonneg hu2,
    Int.toNat_of_nonneg hu3, Int.toNat_of_nonneg hu4, Int.toNat_of_nonneg hu5,
    Int.toNat_of_nonneg hu6, Int.toNat_of_nonneg hv1, Int.toNat_of_nonneg hv2,
    Int.toNat_of_nonneg hv3, Int.toNat_of_nonneg hv4, Int.toNat_of_nonneg hv5,
    Int.toNat_of_nonneg hv6] at h1 h2 h3 h4 h5 h6
  cases u
  cases v
  congr <;> assumption

private theorem ComesFrom.eq_of_common {θ θ' : PlaneIndex} {s t : PrimeTuple} (hne : θ ≠ θ')
    (hs : ComesFrom θ s) (hs' : ComesFrom θ' s)
    (ht : ComesFrom θ t) (ht' : ComesFrom θ' t) : s = t := by
  obtain ⟨u, hu, hus⟩ := hs
  obtain ⟨u', hu', hus'⟩ := hs'
  obtain ⟨v, hv, hvt⟩ := ht
  obtain ⟨v', hv', hvt'⟩ := ht'
  have he := toPrimes_inj hu hu' (hus.trans hus'.symm)
  have hf := toPrimes_inj hv hv' (hvt.trans hvt'.symm)
  have huu : (u.1, u.2) = (u'.1, u'.2) := Plane.lattice_coordinates_of_eq he
  have hvv : (v.1, v.2) = (v'.1, v'.2) := Plane.lattice_coordinates_of_eq hf
  have huu' : u = u' := huu
  have hvv' : v = v' := hvv
  subst u'
  subst v'
  have hθ : (θ.1, θ.2.1, θ.2.2) ≠ (θ'.1, θ'.2.1, θ'.2.2) := hne
  have huv : u = v := Plane.distinct_planes_at_most_one hθ he hf
  subst v
  exact hus.symm.trans hvt

theorem sum_plane_counts_le_union_add_sq (I : Finset PlaneIndex)
    (F : PlaneIndex → Finset PrimeTuple)
    (hF : ∀ i ∈ I, ∀ s ∈ F i, ComesFrom i s) :
    (∑ i ∈ I, (F i).card) ≤ (I.biUnion F).card + I.card ^ 2 := by
  apply sum_card_le_card_biUnion_add_sq
  intro i hi j hj hne
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨hsi, hsj⟩ := Finset.mem_inter.mp hs
  obtain ⟨hti, htj⟩ := Finset.mem_inter.mp ht
  exact ComesFrom.eq_of_common hne (hF i hi s hsi) (hF j hj s hsj)
    (hF i hi t hti) (hF j hj t htj)


theorem sum_plane_counts_le_S_add_sq (I : Finset PlaneIndex)
    (F : PlaneIndex → Finset PrimeTuple) (x : ℝ)
    (h : ∀ i ∈ I, ∀ s ∈ F i, ComesFrom i s ∧ s.IsRealizedBelow x) :
    (∑ i ∈ I, ((F i).card : ℝ)) ≤ S x + (I.card : ℝ) ^ 2 := by
  have hfinite := sum_plane_counts_le_union_add_sq I F (fun i hi s hs => (h i hi s hs).1)
  have hreal : (∑ i ∈ I, ((F i).card : ℝ)) ≤
      ((I.biUnion F).card : ℝ) + (I.card : ℝ) ^ 2 := by
    rw [← Nat.cast_sum]
    exact_mod_cast hfinite
  have hunion : ((I.biUnion F).card : ℝ) ≤ S x := by
    apply card_le_count
    intro s hs
    obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp hs
    exact (h i hi s hsi).2
  exact hreal.trans (add_le_add hunion le_rfl)

end Jsp000881
