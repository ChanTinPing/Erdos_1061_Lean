module

public import Jsp000881.ParameterSieve
import all Jsp000881.ParameterSieve
public import PrimeUniformity.Weights
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

public section

namespace Jsp000881

export PrimeUniformity (primeWeight)

open Filter Asymptotics
open scoped BigOperators Topology

noncomputable def rectanglePrimeMass (θ : PlaneIndex) (T : ℤ) : ℝ :=
  ∑ nm ∈ latticeRectangle T, ∏ i : Fin 6, primeWeight ((sextupleOn θ nm).coord i)

/-- Weighted six-form lower bound on the explicit integral lattice rectangle. -/
def WeightedPrimeRectangleLowerBound : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
    ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
      d * (4 : ℝ) ^ k ≤ rectanglePrimeMass θ ((2 : ℤ) ^ k)

theorem log_scale_upper {k : ℕ} (hk : (1 : ℝ) ≤ (k : ℝ)) :
    Real.log (4000 * (k : ℝ) ^ 14 * (2 : ℝ) ^ k) ≤ 5000 * (k : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (pow_ne_zero _ hk0.ne'), Real.log_pow, Real.log_pow]
  push_cast
  have h₁ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4000 by norm_num)
  have h₂ := Real.log_le_sub_one_of_pos hk0
  have h₃ : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)).trans (by norm_num)
  have h₄ := mul_le_mul_of_nonneg_left h₃ hk0.le
  linarith only [h₁, h₂, h₄, hk]

private theorem prime_weight_upper {k : ℕ} {n : ℤ}
    (hk : (1 : ℝ) ≤ (k : ℝ)) (hn : 127 < n)
    (hhi : n ≤ 4000 * (k : ℤ) ^ 7 * (k : ℤ) ^ 7 * (2 : ℤ) ^ k) :
    0 ≤ primeWeight n ∧ primeWeight n ≤ 5000 * (k : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
  have hn'' : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn'
  have hbound : (n : ℝ) ≤ 4000 * (k : ℝ) ^ 14 * (2 : ℝ) ^ k := by
    have h : (n : ℝ) ≤ 4000 * (k : ℝ) ^ 7 * (k : ℝ) ^ 7 * (2 : ℝ) ^ k :=
      by exact_mod_cast hhi
    convert h using 1 <;> ring
  unfold primeWeight
  split
  · exact ⟨Real.log_nonneg hn', (Real.log_le_log hn'' hbound).trans (log_scale_upper hk)⟩
  · exact ⟨le_rfl, by positivity⟩

private theorem mass_eq_sum_primePoints (θ : PlaneIndex) (T : ℤ) :
    rectanglePrimeMass θ T =
      ∑ nm ∈ primePoints θ T, ∏ i : Fin 6, primeWeight ((sextupleOn θ nm).coord i) := by
  classical
  unfold rectanglePrimeMass primePoints
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro nm hnm hbad
  obtain ⟨i, hi⟩ : ∃ i : Fin 6, ¬ ((sextupleOn θ nm).coord i).toNat.Prime := by
    by_contra h
    push_neg at h
    exact hbad (Finset.mem_filter.mpr ⟨hnm, h⟩)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [primeWeight, hi])

private theorem mass_le_count {k : ℕ} {θ : PlaneIndex}
    (hk : (1 : ℝ) ≤ (k : ℝ)) (hz : 100 ≤ (k : ℤ) ^ 7) (hT : 3 ≤ (2 : ℤ) ^ k)
    (hθ : ParameterBox θ ((k : ℤ) ^ 7)) :
    rectanglePrimeMass θ ((2 : ℤ) ^ k) ≤
      ((primePoints θ ((2 : ℤ) ^ k)).card : ℝ) * (5000 * (k : ℝ)) ^ 6 := by
  classical
  rw [mass_eq_sum_primePoints]
  calc
    _ ≤ ∑ _nm ∈ primePoints θ ((2 : ℤ) ^ k), (5000 * (k : ℝ)) ^ 6 := by
      apply Finset.sum_le_sum
      intro nm hn
      have hnm : nm ∈ latticeRectangle ((2 : ℤ) ^ k) := by
        unfold primePoints at hn
        exact (Finset.mem_filter.mp hn).1
      have hgeom := rectangle_heights hz hT hθ
        ((mem_latticeRectangle (by omega)).mp hnm)
      have hi (i : Fin 6) := prime_weight_upper hk (hgeom.coordinate_large i) (hgeom.coordinate_upper i)
      have hprod :
          (∏ i : Fin 6, primeWeight ((sextupleOn θ nm).coord i)) ≤
            ∏ _ : Fin 6, 5000 * (k : ℝ) := by
        first
        | apply Finset.prod_le_prod₀
        | apply Finset.prod_le_prod
        · exact fun i _ => (hi i).1
        · exact fun i _ => (hi i).2
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem uniformPrimeRectangleLowerBound_of_weighted (h : WeightedPrimeRectangleLowerBound) :
    UniformPrimeRectangleLowerBound := by
  obtain ⟨d, hd, h⟩ := h
  refine ⟨d / (5000 : ℝ) ^ 6, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_large_lattice_scales, h] with k hk hs h
  intro θ hθ ha
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := zero_lt_one.trans_le hk'
  have hb : 0 < (5000 * (k : ℝ)) ^ 6 := by positivity
  have hmain := (h θ hθ ha).trans (mass_le_count hk' hs.1 hs.2 hθ)
  calc
    _ = d * (4 : ℝ) ^ k / (5000 * (k : ℝ)) ^ 6 := by
      field_simp [hk0.ne'] <;> ring
    _ ≤ _ := (div_le_iff₀ hb).mpr hmain

theorem not_linear_asymptotic_of_weighted_prime_rectangle
    (h : WeightedPrimeRectangleLowerBound) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_uniform_prime_rectangle goodParameterFamily
    (uniformPrimeRectangleLowerBound_of_weighted h)

end Jsp000881
