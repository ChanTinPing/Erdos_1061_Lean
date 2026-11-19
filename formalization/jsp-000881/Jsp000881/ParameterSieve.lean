module

public import Jsp000881.Scaled
import all Jsp000881.Scaled
public import Jsp000881.Local
import all Jsp000881.Local
public import Jsp000881.SieveBounds
import all Jsp000881.SieveBounds

public section

namespace Jsp000881

open Filter
open scoped BigOperators

private theorem W_pos : 0 < Plane.W := by decide

private def boxStart (x : ℤ) : ℤ := (x + Plane.W - 1) / Plane.W

private def boxLength (x : ℤ) : ℤ := x / Plane.W

private def boxInterval (x : ℤ) : Finset ℤ := interval (boxStart x) (boxLength x)

private theorem boxLength_nonneg {x : ℤ} (hx : 0 ≤ x) : 0 ≤ boxLength x :=
  Int.ediv_nonneg hx W_pos.le

private theorem boxInterval_bounds {x n : ℤ} (hn : n ∈ boxInterval x) :
    x ≤ Plane.W * n ∧ Plane.W * n ≤ 2 * x := by
  change n ∈ Finset.Ico (boxStart x) (boxStart x + boxLength x) at hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  have hq := Int.ediv_mul_le (x + Plane.W - 1) W_pos.ne'
  have hr := Int.ediv_mul_le x W_pos.ne'
  change boxStart x * Plane.W ≤ x + Plane.W - 1 at hq
  change boxLength x * Plane.W ≤ x at hr
  have hmul := mul_le_mul_of_nonneg_right
    (show n ≤ boxStart x + boxLength x - 1 by omega) W_pos.le
  rw [sub_mul, add_mul, one_mul] at hmul
  constructor
  · exact (Int.le_mul_iff_le_right W_pos).mpr hlo
  · rw [mul_comm Plane.W n]
    omega

private theorem boxLength_real_bounds {x : ℤ} (hx : 2 * Plane.W ≤ x) :
    (x : ℝ) / (2 * (Plane.W : ℝ)) ≤ (boxLength x : ℝ) ∧
      (boxLength x : ℝ) ≤ (x : ℝ) / (Plane.W : ℝ) := by
  have h1 := Int.ediv_mul_le x W_pos.ne'
  have h2 := Int.lt_ediv_add_one_mul_self x W_pos
  change boxLength x * Plane.W ≤ x at h1
  change x < (boxLength x + 1) * Plane.W at h2
  rw [add_mul, one_mul] at h2
  have hq : 1 ≤ boxLength x := by
    change (1 : ℤ) ≤ x / Plane.W
    apply (Int.le_ediv_iff_mul_le W_pos).mpr
    rw [one_mul]
    have := W_pos
    omega
  have hqW := mul_le_mul_of_nonneg_right hq W_pos.le
  rw [one_mul] at hqW
  have h3 : x ≤ boxLength x * (2 * Plane.W) := by
    rw [show boxLength x * (2 * Plane.W) =
      boxLength x * Plane.W + boxLength x * Plane.W by ring]
    omega
  have hW : (0 : ℝ) < (Plane.W : ℝ) := by exact_mod_cast W_pos
  exact ⟨(div_le_iff₀ (by positivity)).mpr (by exact_mod_cast h3),
    (le_div_iff₀ hW).mpr (by exact_mod_cast h1)⟩

private def candidatePlanes (z : ℤ) : Finset PlaneIndex :=
  (boxInterval (z * z)).product ((boxInterval z).product (boxInterval z))

private theorem candidatePlanes_box {z : ℤ} {θ : PlaneIndex} (h : θ ∈ candidatePlanes z) :
    ParameterBox θ z := by
  obtain ⟨ha, hbc⟩ := Finset.mem_product.mp h
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
  exact ⟨(boxInterval_bounds ha).1, (boxInterval_bounds ha).2,
    (boxInterval_bounds hb).1, (boxInterval_bounds hb).2,
    (boxInterval_bounds hc).1, (boxInterval_bounds hc).2⟩

private theorem card_candidatePlanes (z : ℤ) (hz : 0 ≤ z) :
    ((candidatePlanes z).card : ℝ) = (boxLength (z * z) : ℝ) * (boxLength z : ℝ) ^ 2 := by
  simp only [candidatePlanes, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, boxInterval,
    card_interval _ _ (boxLength_nonneg hz), card_interval _ _
      (boxLength_nonneg (mul_nonneg hz hz)), pow_two]

private noncomputable def badRow (z : ℤ) (p : ℕ) (i : Fin 6) : Finset PlaneIndex := by
  classical
  exact (candidatePlanes z).filter fun θ => Plane.BadParameterResidue p θ i

private theorem card_badRow_bound {z : ℤ} {p : ℕ} [hp : Fact p.Prime]
    (hz : 0 ≤ z) (i : Fin 6)
    (e : PlaneIndex → PlaneIndex) (he : Function.Injective e)
    (r₁ r₂ : ℤ → ZMod p)
    (hmaps : ∀ θ ∈ badRow z p i,
      (e θ).1 ∈ boxInterval z ∧ (e θ).2.1 ∈ boxInterval (z * z) ∧
        (e θ).2.2 ∈ boxInterval z ∧ ((e θ).2.1 : ZMod p) = r₁ (e θ).1 ∧
          ((e θ).2.2 : ZMod p) = r₂ (e θ).1) :
    ((badRow z p i).card : ℝ) ≤ (boxLength z : ℝ) *
      ((boxLength (z * z) : ℝ) / p + 1) * ((boxLength z : ℝ) / p + 1) := by
  let C := twoResidueCover (boxInterval z) (boxStart (z * z)) (boxLength (z * z))
    (boxStart z) (boxLength z) r₁ r₂
  have hcard : (badRow z p i).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn e ?_ he.injOn
    intro θ hθ
    obtain ⟨h0, h1, h2, h3, h4⟩ := hmaps θ hθ
    exact mem_twoResidueCover h0 h1 h2 h3 h4
  calc
    _ ≤ (C.card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((boxInterval z).card : ℝ) *
        ((boxLength (z * z) : ℝ) / p + 1) * ((boxLength z : ℝ) / p + 1) :=
      card_twoResidueCover_le hp.out.pos _ _ _ _ _
        (boxLength_nonneg (mul_nonneg hz hz)) (boxLength_nonneg hz) r₁ r₂
    _ = _ := by rw [show ((boxInterval z).card : ℝ) = (boxLength z : ℝ) from
      card_interval _ _ (boxLength_nonneg hz)]

private theorem row_one_bound {z : ℤ} {p : ℕ} [Fact p.Prime]
    (hz : 0 ≤ z) (hw : (Plane.W : ZMod p) ≠ 0) :
    ((badRow z p 1).card : ℝ) ≤ (boxLength z : ℝ) *
      ((boxLength (z * z) : ℝ) / p + 1) * ((boxLength z : ℝ) / p + 1) := by
  classical
  let e : PlaneIndex → PlaneIndex := fun θ => (θ.2.2, θ.1, θ.2.1)
  have he : Function.LeftInverse (fun v : PlaneIndex => (v.2.1, v.2.2, v.1)) e := fun _ => rfl
  refine card_badRow_bound hz 1 e he.injective (fun _ => 0)
    (fun _ => -1 / (462 * (Plane.W : ZMod p))) ?_
  intro θ hθ
  obtain ⟨hθ, hbad⟩ := Finset.mem_filter.mp hθ
  obtain ⟨ha, hbc⟩ := Finset.mem_product.mp hθ
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
  obtain ⟨hr₁, hr₂⟩ := (Plane.parameter_residues_x2 hw θ).mp hbad
  exact ⟨hc, ha, hb, hr₁, hr₂⟩

private theorem rows_three_five_bound {z : ℤ} {p : ℕ} [Fact p.Prime] {i : Fin 6}
    (hz : 0 ≤ z) (r₁ r₂ : ℤ → ZMod p)
    (hr : ∀ θ, Plane.BadParameterResidue p θ i →
      (θ.1 : ZMod p) = r₁ θ.2.1 ∧ (θ.2.2 : ZMod p) = r₂ θ.2.1) :
    ((badRow z p i).card : ℝ) ≤ (boxLength z : ℝ) *
      ((boxLength (z * z) : ℝ) / p + 1) * ((boxLength z : ℝ) / p + 1) := by
  classical
  let e : PlaneIndex → PlaneIndex := fun θ => (θ.2.1, θ.1, θ.2.2)
  have he : Function.LeftInverse e e := fun _ => rfl
  refine card_badRow_bound hz i e he.injective r₁ r₂ ?_
  intro θ hθ
  obtain ⟨hθ, hbad⟩ := Finset.mem_filter.mp hθ
  obtain ⟨ha, hbc⟩ := Finset.mem_product.mp hθ
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
  obtain ⟨hr₁, hr₂⟩ := hr θ hbad
  exact ⟨hb, ha, hc, hr₁, hr₂⟩

private noncomputable def badAt (z : ℤ) (p : ℕ) : Finset PlaneIndex := by
  classical
  exact (candidatePlanes z).filter fun θ => ∃ i, Plane.BadParameterResidue p θ i

private theorem card_badAt_le {z : ℤ} {p : ℕ} [Fact p.Prime] (hz : 0 ≤ z)
    (hw : (Plane.W : ZMod p) ≠ 0) :
    ((badAt z p).card : ℝ) ≤ 3 * (boxLength z : ℝ) *
      ((boxLength (z * z) : ℝ) / p + 1) * ((boxLength z : ℝ) / p + 1) := by
  classical
  have hsub : badAt z p ⊆ badRow z p 1 ∪ badRow z p 3 ∪ badRow z p 5 := by
    intro θ hθ
    obtain ⟨hcand, i, hi⟩ := Finset.mem_filter.mp hθ
    fin_cases i <;> try (simp only [Plane.BadParameterResidue, Plane.DegenerateResidue] at hi)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcand, hi⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcand, hi⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcand, hi⟩)
  have hcard : (badAt z p).card ≤ (badRow z p 1).card + (badRow z p 3).card + (badRow z p 5).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcast : ((badAt z p).card : ℝ) ≤
      ((badRow z p 1).card : ℝ) + ((badRow z p 3).card : ℝ) + ((badRow z p 5).card : ℝ) :=
    by exact_mod_cast hcard
  have h2 := row_one_bound hz hw
  have h4 := rows_three_five_bound hz (i := (3 : Fin 6)) (fun _ => 0)
    (fun _ => -1 / (462 * (Plane.W : ZMod p)))
    (fun θ => (Plane.parameter_residues_x4 hw θ).mp)
  have h6 := rows_three_five_bound hz (i := (5 : Fin 6))
    (fun b => (462 * (Plane.W : ZMod p) * (b : ZMod p) + 1) / (31 * (Plane.W : ZMod p)))
    (fun b => -(462 * 15 * (Plane.W : ZMod p) * (b : ZMod p) + 46) / (462 * 31 * (Plane.W : ZMod p)))
    (fun θ => (Plane.parameter_residues_x6 hw θ).mp)
  linarith only [hcast, h2, h4, h6]

private noncomputable def sievingPrimes (z : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Icc 13 (42550 * z).toNat).filter fun p => p.Prime ∧ (Plane.W : ZMod p) ≠ 0

private noncomputable def badCandidates (z : ℤ) : Finset PlaneIndex :=
  (sievingPrimes z).biUnion (badAt z)

private noncomputable def goodCandidates (z : ℤ) : Finset PlaneIndex :=
  candidatePlanes z \ badCandidates z

private theorem goodCandidates_spec {z : ℤ} (hz : 1 ≤ z) {θ : PlaneIndex}
    (h : θ ∈ goodCandidates z) : ParameterBox θ z ∧ LocallyAdmissible θ := by
  classical
  obtain ⟨hθ, hgood⟩ := Finset.mem_sdiff.mp h
  have hbox := candidatePlanes_box hθ
  refine ⟨hbox, Plane.locallyAdmissible_of_not_badParameterResidue θ ?_⟩
  intro p hp hw i hi
  have hpz := Plane.parameter_bad_prime_le hz hbox i hi
  have hp13 : 13 ≤ p := by have := Plane.prime_twelve_lt_of_W_ne_zero hp hw; omega
  have hpN : p ≤ (42550 * z).toNat :=
    (Int.le_toNat (by omega : 0 ≤ 42550 * z)).mpr hpz
  have hps : p ∈ sievingPrimes z :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp13, hpN⟩, hp, hw⟩
  exact hgood (Finset.mem_biUnion.mpr ⟨p, hps, Finset.mem_filter.mpr ⟨hθ, i, hi⟩⟩)

private theorem badCandidates_subset (z : ℤ) : badCandidates z ⊆ candidatePlanes z := by
  classical
  intro θ hθ
  obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hθ
  exact (Finset.mem_filter.mp hp).1

private theorem count_sievingPrimes {z : ℤ} (hz : 0 ≤ z) :
    ((sievingPrimes z).card : ℝ) ≤ 42550 * (z : ℝ) := by
  classical
  have h : (sievingPrimes z).card ≤ (42550 * z).toNat := by
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    rw [Nat.card_Icc]
    omega
  have h' : ((sievingPrimes z).card : ℤ) ≤ 42550 * z := by
    have hcast : (((42550 * z).toNat : ℕ) : ℤ) = 42550 * z := Int.toNat_of_nonneg (by omega)
    rw [← hcast]
    exact_mod_cast h
  exact_mod_cast h'

private theorem local_sieve_bound {A B P : ℝ} (hB : 0 < B) (hAB : B ≤ A) (hP : 0 < P) :
    3 * B * (A / P + 1) * (B / P + 1) ≤
      (A * B ^ 2) * (6 / P ^ 2 + 6 / B ^ 2) := by
  have hA := hB.trans_le hAB
  have h₁ : 1 / P + 1 / A ≤ 1 / P + 1 / B :=
    add_le_add le_rfl (one_div_le_one_div_of_le hB hAB)
  have h₂ : (1 / P + 1 / B) ^ 2 ≤ 2 / P ^ 2 + 2 / B ^ 2 := by
    have hs := sq_nonneg (1 / P - 1 / B)
    rw [show (2 : ℝ) / P ^ 2 = 2 * (1 / P) ^ 2 by rw [div_pow, one_pow]; ring,
      show (2 : ℝ) / B ^ 2 = 2 * (1 / B) ^ 2 by rw [div_pow, one_pow]; ring]
    nlinarith only [hs]
  calc
    _ = (3 * (A * B ^ 2)) * ((1 / P + 1 / A) * (1 / P + 1 / B)) := by
      field_simp [hA.ne', hB.ne', hP.ne'] <;> ring
    _ ≤ (3 * (A * B ^ 2)) * (1 / P + 1 / B) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (by rw [pow_two]; exact mul_le_mul_of_nonneg_right h₁ (by positivity)) (by positivity)
    _ ≤ (3 * (A * B ^ 2)) * (2 / P ^ 2 + 2 / B ^ 2) :=
      mul_le_mul_of_nonneg_left h₂ (by positivity)
    _ = _ := by ring

private def sieveThreshold : ℤ := 24 * 42550 * (2 * Plane.W) ^ 2

private theorem sieveThreshold_large : 2 * Plane.W ≤ sieveThreshold := by decide

private theorem count_badCandidates {z : ℤ} (hz : sieveThreshold ≤ z) :
    ((badCandidates z).card : ℝ) ≤ 3 / 4 * ((candidatePlanes z).card : ℝ) := by
  classical
  have hzW : 2 * Plane.W ≤ z := sieveThreshold_large.trans hz
  have hz0 : 0 ≤ z := (by decide : 0 ≤ 2 * Plane.W).trans hzW
  have hz1 : 1 ≤ z := (by decide : 1 ≤ 2 * Plane.W).trans hzW
  let A : ℝ := boxLength (z * z)
  let B : ℝ := boxLength z
  let D : ℝ := 2 * (Plane.W : ℝ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (show 0 < 2 * Plane.W by decide)
  have hzr : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hB : 0 < B := (div_pos hzr hD).trans_le (boxLength_real_bounds hzW).1
  have hAB : B ≤ A := by
    have hzsq : z ≤ z * z := by nlinarith only [hz1]
    have hlen : boxLength z ≤ boxLength (z * z) := Int.ediv_le_ediv W_pos hzsq
    change (boxLength z : ℝ) ≤ (boxLength (z * z) : ℝ)
    exact_mod_cast hlen
  have hA := hB.trans_le hAB
  have hmass : ((candidatePlanes z).card : ℝ) = A * B ^ 2 := card_candidatePlanes z hz0
  have hbyP (p : ℕ) (hp : p ∈ sievingPrimes z) :
      ((badAt z p).card : ℝ) ≤ (A * B ^ 2) * (6 / (p : ℝ) ^ 2 + 6 / B ^ 2) := by
    have hp' := (Finset.mem_filter.mp hp).2
    letI : Fact p.Prime := ⟨hp'.1⟩
    exact (card_badAt_le hz0 hp'.2).trans
      (local_sieve_bound hB hAB (by exact_mod_cast hp'.1.pos))
  have hsum : (∑ p ∈ sievingPrimes z, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / 12 :=
    sum_inverse_squares_tail_le 12 (by decide) (sievingPrimes z) fun p hp =>
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have htail : ((sievingPrimes z).card : ℝ) * (6 / B ^ 2) ≤ 1 / 4 := by
    have hupper : ((sievingPrimes z).card : ℝ) ≤ 42550 * (z : ℝ) := count_sievingPrimes hz0
    have hzd : 24 * 42550 * D ^ 2 ≤ (z : ℝ) := by
      dsimp [D]
      exact_mod_cast hz
    have hr : (z : ℝ) / D ≤ B := (boxLength_real_bounds hzW).1
    have hsq : ((z : ℝ) / D) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (div_nonneg hzr.le hD.le) hr 2
    have hthreshold : 24 * (42550 * (z : ℝ)) ≤ ((z : ℝ) / D) ^ 2 := by
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
      calc
        _ = (24 * 42550 * D ^ 2) * (z : ℝ) := by ring
        _ ≤ (z : ℝ) ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hzd hzr.le
    have hmul := mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 24)
    have hP : 24 * ((sievingPrimes z).card : ℝ) ≤ B ^ 2 := hmul.trans (hthreshold.trans hsq)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    linarith only [hP]
  have hbi : ((badCandidates z).card : ℝ) ≤
      ∑ p ∈ sievingPrimes z, ((badAt z p).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.card_biUnion_le :
      (badCandidates z).card ≤ ∑ p ∈ sievingPrimes z, (badAt z p).card)
  have hsix : (∑ p ∈ sievingPrimes z, (6 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / 2 := by
    simp_rw [show ∀ t : ℝ, (6 : ℝ) / t = 6 * (1 / t) from fun t => by ring,
      ← Finset.mul_sum]
    linarith only [hsum]
  calc
    _ ≤ ∑ p ∈ sievingPrimes z, ((badAt z p).card : ℝ) := hbi
    _ ≤ ∑ p ∈ sievingPrimes z, (A * B ^ 2) * (6 / (p : ℝ) ^ 2 + 6 / B ^ 2) :=
      Finset.sum_le_sum hbyP
    _ = (A * B ^ 2) * ((∑ p ∈ sievingPrimes z, (6 : ℝ) / (p : ℝ) ^ 2) +
        ((sievingPrimes z).card : ℝ) * (6 / B ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * B ^ 2) * (3 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsix, htail]) (by positivity)
    _ = _ := by rw [hmass, mul_comm]

private theorem card_bounds_goodCandidates {z : ℤ} (hz : sieveThreshold ≤ z) :
    1 / (4 * (2 * (Plane.W : ℝ)) ^ 3) * (z : ℝ) ^ 4 ≤ ((goodCandidates z).card : ℝ) ∧
      ((goodCandidates z).card : ℝ) ≤ 1 / (Plane.W : ℝ) ^ 3 * (z : ℝ) ^ 4 := by
  classical
  have hzW := sieveThreshold_large.trans hz
  have hz1 : 1 ≤ z := (by decide : 1 ≤ 2 * Plane.W).trans hzW
  have hzsq : 2 * Plane.W ≤ z * z := hzW.trans (by nlinarith only [hz1])
  have hzr : (0 : ℝ) ≤ z := by exact_mod_cast (show 0 ≤ z by omega)
  have hW : (0 : ℝ) < (Plane.W : ℝ) := by exact_mod_cast W_pos
  have hmass := card_candidatePlanes z (by omega)
  have hbad := count_badCandidates hz
  have hcard : ((goodCandidates z).card : ℝ) + ((badCandidates z).card : ℝ) =
      ((candidatePlanes z).card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card (badCandidates_subset z))
  have hsubset : goodCandidates z ⊆ candidatePlanes z := Finset.sdiff_subset
  obtain ⟨hAlo, hAhi⟩ := boxLength_real_bounds hzsq
  obtain ⟨hBlo, hBhi⟩ := boxLength_real_bounds hzW
  push_cast at hAlo hAhi
  have hA0 : (0 : ℝ) ≤ boxLength (z * z) := by
    exact_mod_cast (boxLength_nonneg (mul_self_nonneg z))
  have hB0 : (0 : ℝ) ≤ boxLength z := by exact_mod_cast (boxLength_nonneg (by omega))
  constructor
  · calc
      _ = (1 / 4) * (((z : ℝ) * z / (2 * (Plane.W : ℝ))) *
          ((z : ℝ) / (2 * (Plane.W : ℝ))) ^ 2) := by
        field_simp [hW.ne'] <;> ring
      _ ≤ (1 / 4) * ((boxLength (z * z) : ℝ) * (boxLength z : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul hAlo (pow_le_pow_left₀ (by positivity) hBlo 2) (by positivity) hA0
      _ ≤ _ := by rw [← hmass]; linarith only [hcard, hbad]
  · calc
      _ ≤ ((candidatePlanes z).card : ℝ) := by exact_mod_cast (Finset.card_le_card hsubset)
      _ = _ := hmass
      _ ≤ (((z : ℝ) * z) / (Plane.W : ℝ)) * ((z : ℝ) / (Plane.W : ℝ)) ^ 2 :=
        mul_le_mul hAhi (pow_le_pow_left₀ hB0 hBhi 2) (by positivity) (by positivity)
      _ = _ := by field_simp [hW.ne'] <;> ring

private theorem goodCandidates_family_spec (z : ℤ) (hz : 1 ≤ z) :
    ∀ θ ∈ goodCandidates z, ParameterBox θ z ∧ LocallyAdmissible θ :=
  fun θ hθ => @goodCandidates_spec z hz θ hθ

/-- At least a fixed positive fraction of the parameter box survives the
explicit residue sieve. The only primes to inspect are at most `42550*z`. -/
theorem goodParameterFamily : GoodParameterFamily := by
  unfold GoodParameterFamily
  have hW : (0 : ℝ) < (Plane.W : ℝ) := by exact_mod_cast W_pos
  refine ⟨1 / (4 * (2 * (Plane.W : ℝ)) ^ 3), 1 / (Plane.W : ℝ) ^ 3,
    by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop sieveThreshold.toNat] with k hk
  have hz0 : 0 ≤ sieveThreshold := by decide
  have hkz : sieveThreshold ≤ (k : ℤ) := by
    rw [← Int.toNat_of_nonneg hz0]
    exact_mod_cast hk
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := (by decide : 1 ≤ sieveThreshold).trans hkz
  have hz : sieveThreshold ≤ (k : ℤ) ^ 7 := hkz.trans (le_self_pow₀ hk1 (by decide))
  obtain ⟨hlo, hhi⟩ := card_bounds_goodCandidates hz
  have hp : (((k : ℤ) ^ 7 : ℤ) : ℝ) ^ 4 = (k : ℝ) ^ 28 := by push_cast; ring
  rw [hp] at hlo hhi
  have hpow : 1 ≤ (k : ℤ) ^ 7 := (by decide : 1 ≤ sieveThreshold).trans hz
  exact ⟨goodCandidates ((k : ℤ) ^ 7), hlo, hhi, goodCandidates_family_spec _ hpow⟩

end Jsp000881
