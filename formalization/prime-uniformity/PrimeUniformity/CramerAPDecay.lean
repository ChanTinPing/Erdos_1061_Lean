module

public import PrimeUniformity.CramerAP
public import PrimeUniformity.DyadicSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- A dyadic cutoff gives a progression error bounded by the length of
the ambient interval times a geometric saving in the cutoff index. -/
theorem cramerAP_error_le_dyadic {Q q N k : ℕ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hQ : Q ≤ 2 ^ N) (hN : 4000 ≤ N) (hk : N ^ 4 ≤ k)
    (start len : ℤ) (hlen : 0 ≤ len) (hlen' : len ≤ (2 : ℤ) ^ k)
    (a : ZMod q) (ha : IsUnit a) :
    |(∑ n ∈ residueSlice start len a, cramerWeight Q n) - (len : ℝ) / (q.totient : ℝ)| ≤
      2 * (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ N := by
  let L := cramerDyadicOrder N
  let m := cramerDyadicHalfOrder N
  let S := ∑ p ∈ cramerAPPrimes Q q, (1 : ℝ) / (p : ℝ)
  let T := (2 : ℝ) ^ k
  let F := cramerNormalization Q
  have hQ₀ : 1 ≤ Q := hq.trans_le hqQ
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQR : (Q : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hQ
  have hlenR : (len : ℝ) ≤ T := by dsimp [T]; exact_mod_cast hlen'
  have hlen₀ : 0 ≤ (len : ℝ) := by exact_mod_cast hlen
  have hL : L + 1 = 2 * m := by
    have hm : 1 ≤ m := by simp [m, cramerDyadicHalfOrder]
    dsimp only [L, cramerDyadicOrder]
    change 2 * (m - 1) + 1 + 1 = 2 * m
    omega
  have hS₀ : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by positivity)
  have hS : S ≤ (N : ℝ) + 1 := by
    have hP : cramerAPPrimes Q q ⊆ Finset.range (2 ^ N + 1) := by
      intro p hp
      have hpQ := Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_sdiff.mp hp).1).1
      exact Finset.mem_range.mpr (by omega)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)).trans
      (harmonic_sum_pow_two_le N)
  have hSm : 2 * S ^ 2 ≤ (m : ℝ) + 1 := by
    have hS₂ := pow_le_pow_left₀ hS₀ hS 2
    dsimp [m, cramerDyadicHalfOrder]
    push_cast
    nlinarith only [hS₂, sq_nonneg ((N : ℝ) + 1)]
  have htail : S ^ (L + 1) / ((L + 1).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
    rw [hL]
    exact even_factorial_tail_le hSm
  have hnorm : F ≤ (2 : ℝ) ^ N := (cramerNormalization_le_cutoff hQ₀).trans hQR
  have hF : 0 ≤ F := (cramerNormalization_positive Q).le
  have hD : F * (Q : ℝ) ^ (L + 1) ≤ T * (1 / 2 : ℝ) ^ N := by
    have hExp : N + N * (L + 1) + N ≤ k := by
      have hb := dyadic_exponent_bound hN hk
      change 6 * N + 3 * (N * L) + N ≤ k at hb
      nlinarith only [hb, Nat.zero_le N, Nat.zero_le (N * L)]
    have hNk : N ≤ k := (Nat.le_add_left _ _).trans hExp
    calc
      _ ≤ (2 : ℝ) ^ N * ((2 : ℝ) ^ N) ^ (L + 1) :=
        mul_le_mul hnorm (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQR _) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (N + N * (L + 1)) := by rw [← pow_mul, ← pow_add]
      _ ≤ (2 : ℝ) ^ (k - N) := pow_right_mono₀ (by norm_num) (Nat.le_sub_of_add_le hExp)
      _ = _ := pow_two_times_half hNk
  have hnormTail : F * (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N := by
    have hm : N + N ≤ m := (by omega : N + N ≤ 7 * N).trans (cramerDyadicHalfOrder_ge N)
    calc
      _ ≤ (2 : ℝ) ^ N * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ ≤ (2 : ℝ) ^ N * (1 / 2 : ℝ) ^ (N + N) :=
        mul_le_mul_of_nonneg_left (pow_right_anti₀ (by norm_num) (by norm_num) hm) (by positivity)
      _ = _ := by
        rw [pow_add, one_div, inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have htail0 : 0 ≤ S ^ (L + 1) / ((L + 1).factorial : ℝ) :=
    div_nonneg (pow_nonneg hS₀ _) (Nat.cast_nonneg _)
  have hT0 : 0 ≤ T := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k
  have hM : (len : ℝ) / (q : ℝ) ≤ T := (div_le_self hlen₀ hqR).trans hlenR
  have hb := cramerAP_error_le Q q hq hqQ start len hlen a ha L (cramerDyadicOrder_odd N)
  refine hb.trans ?_
  change F * ((∑ j ∈ Finset.range (L + 2),
    (((cramerAPPrimes Q q).powersetCard j).card : ℝ)) +
    ((len : ℝ) / (q : ℝ)) * (S ^ (L + 1) / ((L + 1).factorial : ℝ))) ≤ _
  calc
    _ ≤ F * ((Q : ℝ) ^ (L + 1) + T * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (cramerAP_truncation_count_le Q q L hQ₀)
          (mul_le_mul hM htail htail0 hT0)) hF
    _ = F * (Q : ℝ) ^ (L + 1) + T * (F * (1 / 2 : ℝ) ^ m) := by ring
    _ ≤ T * (1 / 2 : ℝ) ^ N + T * (1 / 2 : ℝ) ^ N :=
      add_le_add hD (mul_le_mul_of_nonneg_left hnormTail (by positivity))
    _ = _ := by ring

end PrimeUniformity
