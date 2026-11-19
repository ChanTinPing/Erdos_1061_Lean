module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Reciprocal primes in a dyadic block

Primes in the interval `(m, 2m]` divide the middle binomial coefficient.
The binomial expansion bounds their product, then their number and
reciprocal sum. Only the finite factorial and binomial APIs are needed.
-/

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The primes in `(2^n, 2^(n+1)]`. -/
def dyadicPrimeBlock (n : ℕ) : Finset ℕ :=
  (Finset.Ioc ((2 : ℕ) ^ n) ((2 : ℕ) ^ (n + 1))).filter Nat.Prime

theorem mem_dyadicPrimeBlock {n p : ℕ} :
    p ∈ dyadicPrimeBlock n ↔ (2 : ℕ) ^ n < p ∧ p ≤ 2 * (2 : ℕ) ^ n ∧ p.Prime := by
  simp only [dyadicPrimeBlock, Finset.mem_filter, Finset.mem_Ioc, pow_succ, and_assoc]
  rw [mul_comm ((2 : ℕ) ^ n) 2]

private theorem prime_not_dvd_factorial {p m : ℕ} (hp : p.Prime) (hm : m < p) :
    ¬p ∣ m.factorial := by
  revert hm
  induction m with
  | zero =>
    intro _
    simpa using hp.not_dvd_one
  | succ m ih =>
    intro hm hd
    rw [Nat.factorial_succ, hp.dvd_mul] at hd
    rcases hd with hd | hd
    · exact hm.not_ge (Nat.le_of_dvd (Nat.succ_pos m) hd)
    · exact ih ((Nat.lt_succ_self m).trans hm) hd

private theorem prime_dvd_middle_choose {p m : ℕ} (hp : p.Prime) (hlo : m < p)
    (hhi : p ≤ m + m) : p ∣ (m + m).choose m := by
  have hfactorial : p ∣ (m + m).factorial := Nat.dvd_factorial hp.pos hhi
  rw [← Nat.add_choose_mul_factorial_mul_factorial m m] at hfactorial
  have hn := prime_not_dvd_factorial hp hlo
  exact (hp.dvd_mul.mp ((hp.dvd_mul.mp hfactorial).resolve_right hn)).resolve_right hn

theorem dyadicPrimeBlock_card_mul (n : ℕ) :
    n * (dyadicPrimeBlock n).card ≤ 2 * (2 : ℕ) ^ n := by
  let m : ℕ := (2 : ℕ) ^ n
  let P := dyadicPrimeBlock n
  have hmem {p : ℕ} (hp : p ∈ P) : m < p ∧ p ≤ m + m ∧ p.Prime :=
    by simpa only [two_mul] using mem_dyadicPrimeBlock.mp hp
  have hdiv : (∏ p ∈ P, p) ∣ (m + m).choose m :=
    Finset.prod_primes_dvd ((m + m).choose m)
      (fun _ hp => (hmem hp).2.2.prime)
      (fun _ hp => prime_dvd_middle_choose (hmem hp).2.2 (hmem hp).1 (hmem hp).2.1)
  have hchoose_pos : 0 < (m + m).choose m := Nat.choose_pos (Nat.le_add_right _ _)
  have hchoose_top : (m + m).choose m ≤ (2 : ℕ) ^ (m + m) := by
    rw [← Nat.sum_range_choose (m + m)]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_right m m)))
  have hpower : (2 : ℕ) ^ (n * P.card) ≤ (2 : ℕ) ^ (m + m) := by
    rw [pow_mul]
    calc
      _ ≤ ∏ p ∈ P, p := Finset.pow_card_le_prod P id m (fun _ hp => (hmem hp).1.le)
      _ ≤ (m + m).choose m := Nat.le_of_dvd hchoose_pos hdiv
      _ ≤ _ := hchoose_top
  have hcard : n * P.card ≤ m + m :=
    (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hpower
  simpa only [two_mul] using hcard

/-- The reciprocal-prime contribution of one dyadic block above the first
is at most `2/n`. -/
theorem dyadicPrimeBlock_reciprocal_sum_le (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ dyadicPrimeBlock n, (1 : ℝ) / (p : ℝ)) ≤ 2 / (n : ℝ) := by
  let m : ℕ := (2 : ℕ) ^ n
  let P := dyadicPrimeBlock n
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m from pow_pos (by decide : (0 : ℕ) < 2) _)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcard : (n : ℝ) * (P.card : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast dyadicPrimeBlock_card_mul n
  calc
    _ ≤ ∑ _p ∈ P, (1 : ℝ) / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hm (by exact_mod_cast (mem_dyadicPrimeBlock.mp hp).1.le)
    _ = (P.card : ℝ) / (m : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
    _ ≤ _ := (div_le_div_iff₀ hm hn').mpr (by simpa only [mul_comm (P.card : ℝ) (n : ℝ)] using hcard)

end PrimeUniformity
