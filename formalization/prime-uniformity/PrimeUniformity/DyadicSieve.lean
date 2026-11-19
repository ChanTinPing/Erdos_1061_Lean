module

public import PrimeUniformity.CramerBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

def cramerDyadicHalfOrder (N : ℕ) : ℕ := 72 * (N + 1) ^ 2 + 1

def cramerDyadicOrder (N : ℕ) : ℕ := 2 * (cramerDyadicHalfOrder N - 1) + 1

theorem cramerDyadicOrder_odd (N : ℕ) : Odd (cramerDyadicOrder N) := by
  exact ⟨cramerDyadicHalfOrder N - 1, by unfold cramerDyadicOrder; omega⟩

theorem even_factorial_tail_le {x : ℝ} {m : ℕ}
    (h : 2 * x ^ 2 ≤ (m : ℝ) + 1) :
    x ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
  have hm : (m + 1) ^ m ≤ (2 * m).factorial := by
    calc
      _ = 1 * (m + 1) ^ m := (one_mul _).symm
      _ ≤ m.factorial * (m + 1) ^ m :=
        Nat.mul_le_mul_right _ (Nat.factorial_pos _)
      _ ≤ _ := by simpa only [two_mul] using @Nat.factorial_mul_pow_le_factorial m m
  have hm' : ((m : ℝ) + 1) ^ m ≤ ((2 * m).factorial : ℝ) := by exact_mod_cast hm
  have hfact : 0 < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * m)
  have hbase : x ^ 2 ≤ ((m : ℝ) + 1) / 2 := by linarith only [h]
  have hpow := pow_le_pow_left₀ (sq_nonneg x) hbase m
  apply (div_le_iff₀ hfact).mpr
  calc
    x ^ (2 * m) = (x ^ 2) ^ m := pow_mul _ _ _
    _ ≤ (((m : ℝ) + 1) / 2) ^ m := hpow
    _ = ((m : ℝ) + 1) ^ m / (2 : ℝ) ^ m := div_pow _ _ _
    _ ≤ ((2 * m).factorial : ℝ) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hm' (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, one_mul, inv_pow]; ac_rfl

theorem cramerDyadicHalfOrder_ge (N : ℕ) : 7 * N ≤ cramerDyadicHalfOrder N := by
  unfold cramerDyadicHalfOrder
  nlinarith only [Nat.zero_le N, Nat.zero_le (N ^ 2)]

theorem dyadic_exponent_bound {N k : ℕ} (hN : 4000 ≤ N) (hk : N ^ 4 ≤ k) :
    6 * N + 3 * (N * cramerDyadicOrder N) + N ≤ k := by
  have hN' : 1 ≤ N := by omega
  have hs : (N + 1) ^ 2 ≤ (2 * N) ^ 2 :=
    pow_le_pow_left₀ (Nat.zero_le _) (by omega) 2
  have hL : cramerDyadicOrder N ≤ 577 * N ^ 2 := by
    have hs' : 1 ≤ N ^ 2 := one_le_pow₀ hN'
    unfold cramerDyadicOrder cramerDyadicHalfOrder
    rw [Nat.add_sub_cancel]
    nlinarith only [hs, hs']
  have hterm := Nat.mul_le_mul_left (3 * N) hL
  have hN3 : N ≤ N ^ 3 := le_self_pow₀ hN' (by decide)
  have h₀ : 1738 * N ^ 3 ≤ N ^ 4 := by
    calc
      _ ≤ N * N ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  exact (show 6 * N + 3 * (N * cramerDyadicOrder N) + N ≤ 1738 * N ^ 3 by
    nlinarith only [hterm, hN3]).trans (h₀.trans hk)

theorem pow_two_times_half {n j : ℕ} (h : j ≤ n) :
    (2 : ℝ) ^ (n - j) = (2 : ℝ) ^ n * (1 / 2) ^ j := by
  rw [div_pow, one_pow, ← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  rw [← pow_add, Nat.sub_add_cancel h, mul_one]

end PrimeUniformity
