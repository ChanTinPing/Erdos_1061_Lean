module

public import PrimeUniformity.TypeIIBlocks
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

private theorem exists_Icc_of_mem_between (S : Finset ℕ)
    (hS : ∀ ⦃x y z : ℕ⦄, x ∈ S → y ∈ S → x ≤ z → z ≤ y → z ∈ S) :
    ∃ lo hi : ℕ, S = Finset.Icc lo hi := by
  by_cases h : S.Nonempty
  · refine ⟨S.min' h, S.max' h, Finset.ext fun x => ?_⟩
    rw [Finset.mem_Icc]
    exact ⟨fun hx => ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩,
      fun hx => hS (Finset.min'_mem S h) (Finset.max'_mem S h) hx.1 hx.2⟩
  · exact ⟨1, 0, by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩

/-- The canonical parametrization of a residue class reindexes its intersection
with a natural interval by another natural interval. -/
theorem residueClass_Icc_reindex (a b q r : ℕ) (hr : r < q) :
    ∃ lo hi : ℕ, ((Finset.Icc a b).filter fun m => m % q = r) =
      (Finset.Icc lo hi).image (fun x => q * x + r) := by
  let S := (Finset.Icc 0 (b / q)).filter fun x => a ≤ q * x + r ∧ q * x + r ≤ b
  have hmono : Monotone (fun x : ℕ => q * x + r) := fun _ _ h =>
    Nat.add_le_add_right (Nat.mul_le_mul_left q h) r
  obtain ⟨lo, hi, hS⟩ := exists_Icc_of_mem_between S (by
    intro x y z hx hy hxz hzy
    obtain ⟨_, hx'⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy', hy''⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hzy.trans (Finset.mem_Icc.mp hy').2⟩,
        hx'.1.trans (hmono hxz), (hmono hzy).trans hy''.2⟩)
  refine ⟨lo, hi, ?_⟩
  rw [← hS]
  ext m
  constructor
  · intro hm
    obtain ⟨hmem, hmod⟩ := Finset.mem_filter.mp hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
    have he : q * (m / q) + r = m := by
      simpa only [hmod] using Nat.div_add_mod m q
    apply Finset.mem_image.mpr
    refine ⟨m / q, Finset.mem_filter.mpr ⟨?_, ?_⟩, he⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hhi⟩
    · simpa only [he] using And.intro hlo hhi
  · intro hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr (Finset.mem_filter.mp hx).2, ?_⟩
    rw [Nat.add_comm (q * x) r, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The two product cutoffs in a Type II correlation retain an interval of
progression parameters, which may be empty. -/
theorem typeII_progression_filter_eq_Icc (a b L U d e q r : ℕ) :
    ∃ lo hi : ℕ,
      ((Finset.Icc a b).filter fun x =>
        (L ≤ d * (q * x + r) ∧ d * (q * x + r) ≤ U) ∧
        (L ≤ e * (q * x + r) ∧ e * (q * x + r) ≤ U)) = Finset.Icc lo hi := by
  apply exists_Icc_of_mem_between
  intro x y z hx hy hxz hzy
  obtain ⟨hx, hxd, hxe⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hyd, hye⟩ := Finset.mem_filter.mp hy
  have hmono (c : ℕ) : Monotone (fun t : ℕ => c * (q * t + r)) := fun _ _ h =>
    Nat.mul_le_mul_left c (Nat.add_le_add_right (Nat.mul_le_mul_left q h) r)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1.trans hxz, hzy.trans (Finset.mem_Icc.mp hy).2⟩,
      ⟨hxd.1.trans (hmono d hxz), (hmono d hzy).trans hyd.2⟩,
      ⟨hxe.1.trans (hmono e hxz), (hmono e hzy).trans hye.2⟩⟩

private theorem typeII_column_correlation_residue_with_support
    (f : ℕ → ℂ) (a b L U d e q r : ℕ)
    (hr : r < q) :
    ∃ lo hi : ℕ,
      (∀ x ∈ Finset.Icc lo hi, q * x + r ∈ (Finset.Icc a b).filter (fun m => m % q = r)) ∧
      ((∑ m ∈ (Finset.Icc a b).filter (fun m => m % q = r),
        typeIIKernel L U f m d * conj (typeIIKernel L U f m e)) =
      ∑ x ∈ Finset.Icc lo hi, f (d * (q * x + r)) * conj (f (e * (q * x + r)))) := by
  obtain ⟨a', b', hres⟩ := residueClass_Icc_reindex a b q r hr
  have hpos : 0 < q := (Nat.zero_le r).trans_lt hr
  have hinj : Function.Injective (fun x : ℕ => q * x + r) := fun _ _ he =>
    Nat.eq_of_mul_eq_mul_left hpos (Nat.add_right_cancel he)
  obtain ⟨lo, hi, hfilter⟩ := typeII_progression_filter_eq_Icc a' b' L U d e q r
  refine ⟨lo, hi, ?_, ?_⟩
  · intro x hx
    rw [hres]
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp (hfilter.symm ▸ hx)).1, rfl⟩
  · rw [hres, Finset.sum_image hinj.injOn, ← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hd : L ≤ d * (q * x + r) ∧ d * (q * x + r) ≤ U <;>
      by_cases he : L ≤ e * (q * x + r) ∧ e * (q * x + r) ≤ U <;>
      simp [typeIIKernel, Nat.mul_comm (q * x + r) d, Nat.mul_comm (q * x + r) e, hd, he]

/-- A Type II column correlation on one residue class is an unmasked sum on
an interval of progression parameters. -/
theorem typeII_column_correlation_residue (f : ℕ → ℂ) (a b L U d e q r : ℕ)
    (hr : r < q) :
    ∃ lo hi : ℕ,
      (∑ m ∈ (Finset.Icc a b).filter (fun m => m % q = r),
        typeIIKernel L U f m d * conj (typeIIKernel L U f m e)) =
      ∑ x ∈ Finset.Icc lo hi, f (d * (q * x + r)) * conj (f (e * (q * x + r))) := by
  obtain ⟨lo, hi, _, hsum⟩ := typeII_column_correlation_residue_with_support f a b L U d e q r hr
  exact ⟨lo, hi, hsum⟩

/-- At least one residue class keeps a proportion `1/q` of the norm of a
finite sum. -/
theorem exists_large_residue_subsum (s : Finset ℕ) (f : ℕ → ℂ) {q : ℕ} (hq : 0 < q) :
    ∃ r < q, ‖∑ m ∈ s, f m‖ ≤ (q : ℝ) * ‖∑ m ∈ s.filter (fun m => m % q = r), f m‖ := by
  let v (r : ℕ) := ∑ m ∈ s.filter (fun m => m % q = r), f m
  have hmaps (m : ℕ) (_ : m ∈ s) : m % q ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hsum : (∑ r ∈ Finset.range q, v r) = ∑ m ∈ s, f m :=
    Finset.sum_fiberwise_of_maps_to hmaps f
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (Finset.range q) (fun r => ‖v r‖)
    (Finset.nonempty_range_iff.mpr hq.ne')
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  rw [← hsum]
  calc
    _ ≤ ∑ a ∈ Finset.range q, ‖v a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.range q, ‖v r‖ := Finset.sum_le_sum hmax
    _ = (q : ℝ) * ‖v r‖ := by simp [nsmul_eq_mul]

/-- Many sums with large norm have one common residue that keeps their
correlation, losing a factor `q` in both the count and the norm. -/
theorem exists_common_large_residue_subsums {ι : Type*}
    (T : Finset ι) (s : Finset ℕ) (F : ι → ℕ → ℂ) {q : ℕ} (hq : 0 < q) (H : ℝ)
    (hlarge : ∀ i ∈ T, H ≤ ‖∑ m ∈ s, F i m‖) :
    ∃ r < q, ∃ U ⊆ T, (T.card : ℝ) / q ≤ U.card ∧
      ∀ i ∈ U, H ≤ (q : ℝ) * ‖∑ m ∈ s.filter (fun m => m % q = r), F i m‖ := by
  classical
  choose r hr hbound using fun i : ι => exists_large_residue_subsum s (F i) hq
  have hmaps (i : ι) (_ : i ∈ T) : r i ∈ Finset.range q := Finset.mem_range.mpr (hr i)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hsize : (Finset.range q).card • ((T.card : ℝ) / (q : ℝ)) ≤ (T.card : ℝ) := by
    rw [Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hqR.ne']
  obtain ⟨j, hj, hJ⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps (Finset.nonempty_range_iff.mpr hq.ne') hsize
  refine ⟨j, Finset.mem_range.mp hj, T.filter (fun i => r i = j), Finset.filter_subset _ _, hJ,
    fun i hi => ?_⟩
  obtain ⟨hiT, heq⟩ := Finset.mem_filter.mp hi
  exact (hlarge i hiT).trans (heq ▸ hbound i)

/-- For large Type II column correlations with progression support, fix
one common residue class of the row variable. The two dilated tests are
then unmasked over an interval whose length is at least the retained norm. -/
theorem exists_common_large_vaughan_dilation_subsums_with_support (T : Finset (ℕ × ℕ))
    (a b L X q z : ℕ) (hq : 0 < q) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {H : ℝ} (hH : 0 < H) :
    let A := (Finset.Icc L X).filter (fun n => n % q = z)
    let K := vaughanTypeIIKernel A f
    (∀ p ∈ T, H ≤ ‖∑ m ∈ Finset.Icc a b, K m p.1 * conj (K m p.2)‖) →
    ∃ r < q, ∃ J ⊆ T, (T.card : ℝ) / q ≤ J.card ∧
      ∀ p ∈ J, (p.1 * r) % q = z ∧ (p.2 * r) % q = z ∧
        ∃ lo hi : ℕ, lo ≤ hi ∧
          (∀ x ∈ Finset.Icc lo hi, q * x + r ∈ Finset.Icc a b) ∧
          H / (q : ℝ) ≤ ((Finset.Icc lo hi).card : ℝ) ∧
          H / (q : ℝ) ≤ ‖∑ x ∈ Finset.Icc lo hi,
            f (p.1 * (q * x + r)) * conj (f (p.2 * (q * x + r)))‖ ∧
          (H / (q : ℝ)) / ((Finset.Icc a b).card : ℝ) ≤
            ‖∑ x ∈ Finset.Icc lo hi, f (p.1 * (q * x + r)) * conj (f (p.2 * (q * x + r)))‖ /
              ((Finset.Icc lo hi).card : ℝ) := by
  intro A K hlarge
  obtain ⟨r, hr, J, hJ, hcard, hsubsum⟩ :=
    exists_common_large_residue_subsums T (Finset.Icc a b)
      (fun p m => K m p.1 * conj (K m p.2)) hq H hlarge
  refine ⟨r, hr, J, hJ, hcard, ?_⟩
  intro p hp
  let R := (Finset.Icc a b).filter (fun m => m % q = r)
  have hR := hsubsum p hp
  have hmod (d m : ℕ) (hm : m ∈ R) : (m * d) % q = (d * r) % q := by
    rw [Nat.mul_comm m d, Nat.mul_mod d m, (Finset.mem_filter.mp hm).2, Nat.mul_mod d r,
      Nat.mod_eq_of_lt hr]
  have hzero (d m : ℕ) (hm : m ∈ R) (hz : (d * r) % q ≠ z) : K m d = 0 := by
    have hnot : m * d ∉ A := by
      intro hn
      exact hz ((hmod d m hm).symm.trans (Finset.mem_filter.mp hn).2)
    simp [K, vaughanTypeIIKernel, hnot]
  have hd : (p.1 * r) % q = z := by
    by_contra h
    have he : (∑ m ∈ R, K m p.1 * conj (K m p.2)) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [hzero p.1 m hm h, zero_mul]
    change H ≤ (q : ℝ) * ‖∑ m ∈ R, K m p.1 * conj (K m p.2)‖ at hR
    rw [he, norm_zero, mul_zero] at hR
    exact (not_le_of_gt hH) hR
  have he : (p.2 * r) % q = z := by
    by_contra h
    have he : (∑ m ∈ R, K m p.1 * conj (K m p.2)) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [hzero p.2 m hm h, map_zero, mul_zero]
    change H ≤ (q : ℝ) * ‖∑ m ∈ R, K m p.1 * conj (K m p.2)‖ at hR
    rw [he, norm_zero, mul_zero] at hR
    exact (not_le_of_gt hH) hR
  have hunmask (d m : ℕ) (hm : m ∈ R) (hd : (d * r) % q = z) :
      K m d = typeIIKernel L X f m d := by
    simp only [K, vaughanTypeIIKernel, A, Finset.mem_filter, Finset.mem_Icc,
      hmod d m hm, hd, and_true, typeIIKernel]
  have hsame : (∑ m ∈ R, K m p.1 * conj (K m p.2)) =
      ∑ m ∈ R, typeIIKernel L X f m p.1 * conj (typeIIKernel L X f m p.2) :=
    Finset.sum_congr rfl fun m hm => by rw [hunmask _ _ hm hd, hunmask _ _ hm he]
  obtain ⟨lo, hi, hsupp, hinterval⟩ :=
    typeII_column_correlation_residue_with_support f a b L X p.1 p.2 q r hr
  change H ≤ (q : ℝ) * ‖∑ m ∈ R, K m p.1 * conj (K m p.2)‖ at hR
  rw [hsame, hinterval, mul_comm (q : ℝ)] at hR
  have hlower := (div_le_iff₀ (Nat.cast_pos.mpr hq)).mpr hR
  have hlen := hlower.trans (calc
    _ ≤ ∑ x ∈ Finset.Icc lo hi, ‖f (p.1 * (q * x + r)) * conj (f (p.2 * (q * x + r)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.Icc lo hi, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
    _ = ((Finset.Icc lo hi).card : ℝ) := by simp)
  have hlenpos : 0 < ((Finset.Icc lo hi).card : ℝ) :=
    (div_pos hH (Nat.cast_pos.mpr hq)).trans_le hlen
  have hlohi := Finset.nonempty_Icc.mp (Finset.card_pos.mp (Nat.cast_pos.mp hlenpos))
  have hmem x (hx : x ∈ Finset.Icc lo hi) : q * x + r ∈ Finset.Icc a b :=
    (Finset.mem_filter.mp (hsupp x hx)).1
  have hcard' : ((Finset.Icc lo hi).card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : ℕ => q * x + r) hmem
      (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel he))
  refine ⟨hd, he, lo, hi, hlohi, hmem, hlen, hlower, ?_⟩
  exact (div_le_div_of_nonneg_left (div_nonneg hH.le (Nat.cast_nonneg q)) hlenpos hcard').trans
    (div_le_div_of_nonneg_right hlower hlenpos.le)

/-- Fix one common row residue and extract interval samples without the
progression mask. -/
theorem exists_common_large_vaughan_dilation_subsums (T : Finset (ℕ × ℕ))
    (a b L X q z : ℕ) (hq : 0 < q) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {H : ℝ} (hH : 0 < H) :
    let A := (Finset.Icc L X).filter (fun n => n % q = z)
    let K := vaughanTypeIIKernel A f
    (∀ p ∈ T, H ≤ ‖∑ m ∈ Finset.Icc a b, K m p.1 * conj (K m p.2)‖) →
    ∃ r < q, ∃ J ⊆ T, (T.card : ℝ) / q ≤ J.card ∧
      ∀ p ∈ J, (p.1 * r) % q = z ∧ (p.2 * r) % q = z ∧
        ∃ lo hi : ℕ, H / (q : ℝ) ≤ ((Finset.Icc lo hi).card : ℝ) ∧
          H / (q : ℝ) ≤ ‖∑ x ∈ Finset.Icc lo hi,
            f (p.1 * (q * x + r)) * conj (f (p.2 * (q * x + r)))‖ := by
  intro A K hlarge
  obtain ⟨r, hr, J, hJ, hcard, hsamples⟩ :=
    exists_common_large_vaughan_dilation_subsums_with_support T a b L X q z hq f hf hH hlarge
  refine ⟨r, hr, J, hJ, hcard, fun p hp => ?_⟩
  obtain ⟨hd, he, lo, hi, _, _, hlen, hsum, _⟩ := hsamples p hp
  exact ⟨hd, he, lo, hi, hlen, hsum⟩

end PrimeUniformity
