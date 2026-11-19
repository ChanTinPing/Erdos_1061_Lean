module

public import PrimeUniformity.TypeIPrefixes
public import PrimeUniformity.TypeIIProgressions
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

private theorem typeIPrefixProgression_eq_image {U V q r d k : ℕ} (hd : 0 < d) :
    (((Finset.Ioc U V).filter (fun n => n % q = r)).filter (· ≤ d * k)).filter (d ∣ ·) =
      ((Finset.Icc (U / d + 1) (min k (V / d))).filter (fun m => (d * m) % q = r)).image
        (d * ·) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc, le_min_iff]
  have hlow (m : ℕ) : U / d + 1 ≤ m ↔ U < d * m := by
    rw [Nat.succ_le_iff, Nat.div_lt_iff_lt_mul hd, Nat.mul_comm m d]
  have hhigh (m : ℕ) : m ≤ V / d ↔ d * m ≤ V := by
    rw [Nat.le_div_iff_mul_le hd, Nat.mul_comm m d]
  constructor
  · rintro ⟨⟨⟨⟨hU, hV⟩, hr⟩, hk⟩, m, rfl⟩
    exact ⟨m, ⟨⟨(hlow m).mpr hU,
      Nat.le_of_mul_le_mul_left hk hd, (hhigh m).mpr hV⟩, hr⟩, rfl⟩
  · rintro ⟨m, ⟨⟨hU, hk, hV⟩, hr⟩, rfl⟩
    exact ⟨⟨⟨⟨(hlow m).mp hU, (hhigh m).mp hV⟩, hr⟩,
      Nat.mul_le_mul_left d hk⟩, ⟨m, rfl⟩⟩

/-- A nonempty Type I fiber in a progression prefix is exactly an affine
image of an interval. The cofactor stride is the exact period q / gcd q d. -/
theorem typeIPrefix_progression_image {U V q r d k : ℕ} (hd : 0 < d) (hq : 0 < q)
    (hS : ((((Finset.Ioc U V).filter (fun n => n % q = r)).filter (· ≤ d * k)).filter
      (d ∣ ·)).Nonempty) :
    let Q := q / Nat.gcd q d
    ∃ b < Q, ∃ lo hi : ℕ,
      (((Finset.Ioc U V).filter (fun n => n % q = r)).filter (· ≤ d * k)).filter (d ∣ ·) =
        (Finset.Icc lo hi).image (fun x => d * (Q * x + b)) := by
  intro Q
  let I := Finset.Icc (U / d + 1) (min k (V / d))
  have himage := typeIPrefixProgression_eq_image (U := U) (V := V) (q := q) (r := r)
    (k := k) hd
  rw [himage] at hS ⊢
  obtain ⟨n, hn⟩ := hS
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hn
  have hr₀ : (d * m₀) % q = r := (Finset.mem_filter.mp hm₀).2
  have hQ : 0 < Q := Nat.div_pos (Nat.gcd_le_left d hq) (Nat.gcd_pos_of_pos_left d hq)
  let b := m₀ % Q
  have hb : b < Q := Nat.mod_lt _ hQ
  have hdQ : q ∣ d * Q := by
    have hg : q ∣ Nat.gcd q d * Q := by
      dsimp only [Q]
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left q d)]
    exact hg.trans (Nat.mul_dvd_mul_right (Nat.gcd_dvd_right q d) Q)
  have hres (m : ℕ) : (d * m) % q = r ↔ m % Q = b := by
    rw [← hr₀]
    change (d * m ≡ d * m₀ [MOD q]) ↔ (m ≡ m₀ [MOD Q])
    exact ⟨Nat.ModEq.cancel_left_div_gcd hq, fun h => (h.mul_left' d).of_dvd hdQ⟩
  have hfilter : I.filter (fun m => (d * m) % q = r) = I.filter (fun m => m % Q = b) :=
    Finset.filter_congr fun m _ => hres m
  obtain ⟨lo, hi, hcell⟩ := residueClass_Icc_reindex (U / d + 1) (min k (V / d)) Q b hb
  refine ⟨b, hb, lo, hi, ?_⟩
  change (I.filter (fun m => (d * m) % q = r)).image (d * ·) = _
  rw [hfilter, hcell, Finset.image_image]
  rfl

/-- A positive Type I prefix correlation transfers in full to its affine
cell. For a one-bounded test the cell has at least the given threshold
many points and at most X / d points. -/
theorem typeIPrefix_progression_subsum {X U V q r d k : ℕ}
    (hVX : V ≤ X) (hd : 0 < d) (hq : 0 < q) (F : ℕ → ℂ) {H : ℝ} (hH : 0 < H) :
    let A := (Finset.Ioc U V).filter (fun n => n % q = r)
    let Q := q / Nat.gcd q d
    (∀ n ∈ A, ‖F n‖ ≤ 1) →
    H ≤ ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖ →
    ∃ b < Q, ∃ lo hi : ℕ,
      (∀ x ∈ Finset.Icc lo hi, d * (Q * x + b) ∈ A.filter (· ≤ d * k)) ∧
      divisorCorrelation (A.filter (· ≤ d * k)) F d =
        (∑ x ∈ Finset.Icc lo hi, F (d * (Q * x + b))) ∧
      H ≤ ‖∑ x ∈ Finset.Icc lo hi, F (d * (Q * x + b))‖ ∧
      H ≤ ((Finset.Icc lo hi).card : ℝ) ∧
      (Finset.Icc lo hi).card ≤ X / d := by
  intro A Q hF hlarge
  let S := (A.filter (· ≤ d * k)).filter (d ∣ ·)
  have hS : S.Nonempty := by
    by_contra h
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    change H ≤ ‖∑ n ∈ S, F n‖ at hlarge
    simp only [hz, Finset.sum_empty, norm_zero] at hlarge
    exact (not_le_of_gt hH) hlarge
  obtain ⟨b, hb, lo, hi, himage⟩ := typeIPrefix_progression_image hd hq hS
  let g (x : ℕ) := d * (Q * x + b)
  change S = (Finset.Icc lo hi).image g at himage
  have hQ : 0 < Q := (Nat.zero_le b).trans_lt hb
  have hg : Function.Injective g := fun _ _ he =>
    Nat.eq_of_mul_eq_mul_left hQ (Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hd he))
  have hmem (x : ℕ) (hx : x ∈ Finset.Icc lo hi) : g x ∈ A.filter (· ≤ d * k) := by
    have hm : g x ∈ S := himage.symm ▸ Finset.mem_image_of_mem g hx
    exact (Finset.mem_filter.mp hm).1
  have heq : divisorCorrelation (A.filter (· ≤ d * k)) F d =
      ∑ x ∈ Finset.Icc lo hi, F (g x) := by
    change (∑ n ∈ S, F n) = _
    rw [himage, Finset.sum_image hg.injOn]
  have hnorm : ‖∑ x ∈ Finset.Icc lo hi, F (g x)‖ ≤ ((Finset.Icc lo hi).card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _x ∈ Finset.Icc lo hi, (1 : ℝ) :=
        Finset.sum_le_sum fun x hx => hF _ (Finset.mem_filter.mp (hmem x hx)).1
      _ = _ := by simp
  have hsub : S ⊆ (Finset.Ioc 0 X).filter (d ∣ ·) := by
    intro n hn
    obtain ⟨hnUV, _⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    obtain ⟨hU, hV⟩ := Finset.mem_Ioc.mp hnUV
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt hU, hV.trans hVX⟩,
      (Finset.mem_filter.mp hn).2⟩
  have hcard : (Finset.Icc lo hi).card = S.card := by
    rw [himage, Finset.card_image_of_injective _ hg]
  rw [heq] at hlarge
  refine ⟨b, hb, lo, hi, hmem, heq, hlarge, hlarge.trans hnorm, ?_⟩
  exact (hcard.trans_le (Finset.card_le_card hsub)).trans_eq (Nat.Ioc_filter_dvd_card_eq_div X d)

/-- Each factor in the selected dense Type I block gives an unmasked
dilation sum with nonempty interval, quantitative length and mean. -/
theorem exists_dense_large_typeI_dilation_subsums {X D U V q r : ℕ}
    (hX : 0 < X) (hVX : V ≤ X) (hq : 0 < q) (F : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    let A := (Finset.Ioc U V).filter (fun n => n % q = r)
    (∀ n ∈ A, ‖F n‖ ≤ 1) →
    DenseTypeIPrefixes X D A F δ →
    ∃ i ≤ Nat.log 2 D, ∃ T ⊆ dyadicFactorBlock 0 D i, (δ / 2) * (2 : ℝ) ^ i ≤ (T.card : ℝ) ∧
      ∀ d ∈ T, let Q := q / Nat.gcd q d
        ∃ b < Q, ∃ lo hi : ℕ,
          (∀ x ∈ Finset.Icc lo hi, d * (Q * x + b) ∈ A) ∧
          (δ / 2) * ((X : ℝ) / 2 ^ i) ≤ ((Finset.Icc lo hi).card : ℝ) ∧
          (Finset.Icc lo hi).card ≤ X / d ∧
          δ / 2 ≤ ‖∑ x ∈ Finset.Icc lo hi, F (d * (Q * x + b))‖ /
            ((Finset.Icc lo hi).card : ℝ) := by
  intro A hF hDense
  obtain ⟨i, hi, hcard, hlarge⟩ := hDense
  let B := dyadicFactorBlock 0 D i
  let H := (δ / 2) * ((X : ℝ) / 2 ^ i)
  let T := B.filter (fun d => H ≤ typeIPrefixMax X d A F)
  have hH : 0 < H := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    dsimp only [H]
    positivity
  refine ⟨i, hi, T, Finset.filter_subset _ _, hcard, ?_⟩
  intro d hdT
  obtain ⟨hd, _, hdi, _⟩ := mem_dyadicFactorBlock.mp (Finset.mem_filter.mp hdT).1
  obtain ⟨k, _, hk⟩ := hlarge d hdT
  obtain ⟨b, hb, lo, hi, hmem, _, hnorm, hlen, hlen'⟩ :=
    typeIPrefix_progression_subsum hVX hd hq F hH hF hk
  refine ⟨b, hb, lo, hi, fun x hx => (Finset.mem_filter.mp (hmem x hx)).1, hlen, hlen', ?_⟩
  have hpos : (0 : ℝ) < (Finset.Icc lo hi).card := hH.trans_le hlen
  apply (le_div_iff₀ hpos).mpr
  refine (mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ δ / 2)).trans hnorm
  refine (show ((Finset.Icc lo hi).card : ℝ) ≤ ((X / d : ℕ) : ℝ) by exact_mod_cast hlen').trans ?_
  exact Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (by exact_mod_cast hdi))

end PrimeUniformity
