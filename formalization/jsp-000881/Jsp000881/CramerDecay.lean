module

public import PrimeUniformity.DyadicSieve
public import Jsp000881.CramerHarmonic
public import Jsp000881.CramerMass

@[expose] public section

namespace Jsp000881

open Filter Asymptotics
open scoped BigOperators Topology

export PrimeUniformity (cramerDyadicOrder cramerDyadicOrder_odd cramerDyadicHalfOrder cramerDyadicHalfOrder_ge)

/-- The dyadic upper bound for the prime cutoff gives an explicit vanishing
budget with a quadratic truncation order in its logarithm. -/
theorem cramerBoxBudget_le_dyadic {Q N k : ℕ} (hQ₀ : 1 ≤ Q) (hQ : Q ≤ 2 ^ N)
    (hN : 4000 ≤ N) (hk : N ^ 4 ≤ k) (θ : PlaneIndex) (hθ : LocallyAdmissible θ)
    {a b : ℤ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha' : a ≤ (2 : ℤ) ^ k) (hb' : b ≤ (2 : ℤ) ^ k) :
    cramerBoxBudget Q θ a b (cramerDyadicOrder N) ≤
      4 * (1 / 2 : ℝ) ^ N * (4 : ℝ) ^ k := by
  let L := cramerDyadicOrder N
  let m := cramerDyadicHalfOrder N
  let T : ℝ := (2 : ℝ) ^ k
  let q : ℝ := Q
  let D := q ^ L
  let S := ∑ p ∈ cramerPrimeSet Q, localBadDensity θ p
  have hL : L + 1 = 2 * m := by
    have hm : 1 ≤ m := by simp [m, cramerDyadicHalfOrder]
    dsimp only [L, cramerDyadicOrder]
    change 2 * (m - 1) + 1 + 1 = 2 * m
    have he := Nat.sub_add_cancel hm
    nlinarith only [he]
  have hS : S ≤ 6 * ((N : ℝ) + 1) := sum_cramerBadDensity_le_dyadic θ hθ Q N hQ
  have hS₀ : 0 ≤ S := Finset.sum_nonneg fun p hp =>
    (localBadDensity_bounds θ (Finset.mem_filter.mp hp).2).1
  have hS₁ := pow_le_pow_left₀ hS₀ hS 2
  have hSm : 2 * S ^ 2 ≤ (m : ℝ) + 1 := by
    dsimp only [m, cramerDyadicHalfOrder]
    push_cast
    nlinarith only [hS₁]
  have htail : S ^ (L + 1) / ((L + 1).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
    rw [hL]
    exact PrimeUniformity.even_factorial_tail_le hSm
  have hq₀ : (1 : ℝ) ≤ q := by dsimp only [q]; exact_mod_cast hQ₀
  have hq : q ≤ (2 : ℝ) ^ N := by dsimp only [q]; exact_mod_cast hQ
  have hq6 : q ^ 6 ≤ (2 : ℝ) ^ (6 * N) := by
    rw [mul_comm 6 N, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hq 6
  have hD : D ≤ (2 : ℝ) ^ (N * L) := by
    dsimp only [D]
    rw [pow_mul]
    exact pow_le_pow_left₀ (zero_le_one.trans hq₀) hq L
  have hD₀ : (1 : ℝ) ≤ D := by
    exact one_le_pow₀ hq₀
  have hscalar : 0 ≤ S ^ (L + 1) / ((L + 1).factorial : ℝ) :=
    div_nonneg (pow_nonneg hS₀ _) (Nat.cast_nonneg _)
  have htail' : q ^ 6 * (S ^ (L + 1) / ((L + 1).factorial : ℝ)) ≤ (1 / 2 : ℝ) ^ N := by
    have hlow : N + 6 * N ≤ m := by
      have he : N + 6 * N = 7 * N := by ring
      rw [he]
      exact cramerDyadicHalfOrder_ge N
    calc
      _ ≤ (2 : ℝ) ^ (6 * N) * (1 / 2 : ℝ) ^ m :=
        mul_le_mul hq6 htail hscalar (by positivity)
      _ ≤ (2 : ℝ) ^ (6 * N) * (1 / 2 : ℝ) ^ (N + 6 * N) :=
        mul_le_mul_of_nonneg_left (pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hlow)
          (by positivity)
      _ = _ := by
        rw [pow_add, show (1 / 2 : ℝ) ^ (6 * N) = ((2 : ℝ) ^ (6 * N))⁻¹ by
          rw [div_pow, one_pow, one_div]]
        have hc : (2 : ℝ) ^ (6 * N) ≠ 0 := by positivity
        calc
          _ = ((2 : ℝ) ^ (6 * N) * ((2 : ℝ) ^ (6 * N))⁻¹) * (1 / 2 : ℝ) ^ N := by ac_rfl
          _ = _ := by rw [mul_inv_cancel₀ hc, one_mul]
  have hD3 : q ^ 6 * D ^ 3 ≤ T * (1 / 2 : ℝ) ^ N := by
    have hExp : 6 * N + 3 * (N * L) + N ≤ k := PrimeUniformity.dyadic_exponent_bound hN hk
    have hExp' : 6 * N + 3 * (N * L) ≤ k - N := Nat.le_sub_of_add_le hExp
    have hNk : N ≤ k := (Nat.le_add_left _ _).trans hExp
    calc
      _ ≤ (2 : ℝ) ^ (6 * N) * ((2 : ℝ) ^ (N * L)) ^ 3 :=
        mul_le_mul hq6 (pow_le_pow_left₀ (by positivity) hD 3) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (6 * N + 3 * (N * L)) := by
        rw [pow_add, mul_comm 3 (N * L), pow_mul _ (N * L) 3]
      _ ≤ (2 : ℝ) ^ (k - N) := pow_right_mono₀ (by norm_num) hExp'
      _ = _ := PrimeUniformity.pow_two_times_half hNk
  have hD2 : q ^ 6 * D ^ 2 ≤ T * (1 / 2 : ℝ) ^ N :=
    (mul_le_mul_of_nonneg_left (pow_right_mono₀ hD₀ (by norm_num)) (by positivity)).trans hD3
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hT2 : T ^ 2 = (4 : ℝ) ^ k := by
    dsimp [T]
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  refine (cramerBoxBudget_le hQ₀ θ ha₀ hb₀ ha' hb').trans ?_
  push_cast
  change q ^ 6 * (T ^ 2 * (S ^ (L + 1) / ((L + 1).factorial : ℝ)) + 2 * T * D ^ 2 + D ^ 3) ≤ _
  calc
    _ = T ^ 2 * (q ^ 6 * (S ^ (L + 1) / ((L + 1).factorial : ℝ))) +
        2 * T * (q ^ 6 * D ^ 2) + q ^ 6 * D ^ 3 := by ring
    _ ≤ T ^ 2 * (1 / 2 : ℝ) ^ N + 2 * T * (T * (1 / 2 : ℝ) ^ N) +
        T * (1 / 2 : ℝ) ^ N :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left htail' (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hD2 (by positivity))) hD3
    _ ≤ 4 * (1 / 2 : ℝ) ^ N * (4 : ℝ) ^ k := by
      rw [← hT2]
      have hTT : T ≤ T ^ 2 := le_self_pow₀ hT1 (by decide)
      have hp := mul_le_mul_of_nonneg_right hTT (show (0 : ℝ) ≤ (1 / 2) ^ N by positivity)
      linarith only [hp]

theorem cramerTruncationBudget_le_dyadic {Q N k : ℕ} (hQ₀ : 1 ≤ Q) (hQ : Q ≤ 2 ^ N)
    (hN : 4000 ≤ N) (hk : N ^ 4 ≤ k) (θ : PlaneIndex) (hθ : LocallyAdmissible θ) :
    cramerTruncationBudget Q θ ((2 : ℤ) ^ k) (cramerDyadicOrder N) ≤
      4 * (1 / 2 : ℝ) ^ N * (4 : ℝ) ^ k := by
  have h34 : 34 ≤ k := calc
    34 ≤ N := (by decide : 34 ≤ 4000).trans hN
    _ ≤ N ^ 4 := le_self_pow₀ ((by decide : 1 ≤ 4000).trans hN) (by decide)
    _ ≤ k := hk
  have hT : (10000000000 : ℤ) ≤ (2 : ℤ) ^ k :=
    (by norm_num : (10000000000 : ℤ) ≤ (2 : ℤ) ^ 34).trans
      (pow_right_mono₀ (by norm_num) h34)
  obtain ⟨ha, ha', hb, hb'⟩ := rectangle_length_bounds hT
  have hTr : (0 : ℝ) ≤ ↑((2 : ℤ) ^ k) := by exact_mod_cast (show (0 : ℤ) ≤ 2 ^ k by positivity)
  exact cramerBoxBudget_le_dyadic hQ₀ hQ hN hk θ hθ
    (by exact_mod_cast (div_nonneg hTr (by norm_num)).trans ha)
    (by exact_mod_cast (div_nonneg hTr (by norm_num)).trans hb)
    (by exact_mod_cast ha') (by exact_mod_cast hb')

/-- For every cutoff satisfying the stated elementary dyadic growth
conditions the Cramér main term is uniformly positive. -/
theorem uniformCramerMassLowerBound_of_dyadic_growth (cutoff N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hgrowth : ∀ᶠ k in atTop, 1 ≤ cutoff k ∧ cutoff k ≤ 2 ^ N k ∧ N k ^ 4 ≤ k) :
    UniformCramerMassLowerBound cutoff := by
  apply uniformCramerMassLowerBound_of_small_budget cutoff (fun k => cramerDyadicOrder (N k))
  · filter_upwards [] with k
    exact cramerDyadicOrder_odd _
  · intro ε hε
    have ht : Tendsto (fun k => 4 * (1 / 2 : ℝ) ^ N k) atTop (𝓝 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
      simpa only [mul_zero, Function.comp_apply] using (hp.comp hN).const_mul 4
    filter_upwards [hgrowth, hN.eventually (eventually_ge_atTop (4000 : ℕ)),
      (tendsto_order.1 ht).2 ε hε] with k hk hlarge hsmall
    intro θ _ hθ
    exact (cramerTruncationBudget_le_dyadic hk.1 hk.2.1 hlarge hk.2.2 θ hθ).trans
      (mul_le_mul_of_nonneg_right hsmall.le (by positivity))

/-- After the finite model estimate, only the six replacement errors remain
in this conditional proof of the original asymptotic statement. -/
theorem not_linear_asymptotic_of_dyadic_replacement (cutoff N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hgrowth : ∀ᶠ k in atTop, 1 ≤ cutoff k ∧ cutoff k ≤ 2 ^ N k ∧ N k ^ 4 ≤ k)
    (herror : UniformRectangleReplacementError cutoff) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_weighted_prime_rectangle
    (weightedPrimeRectangleLowerBound_of_model (uniformCramerMassLowerBound_of_dyadic_growth cutoff N hN hgrowth) herror)

end Jsp000881
