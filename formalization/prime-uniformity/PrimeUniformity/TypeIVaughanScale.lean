module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

/-- The square-root cutoff leaves an exponentially large cofactor scale
on every dyadic Type I band once the original interval is sufficiently long. -/
theorem typeI_vaughan_cofactor_exp_lower {X i : ℕ} (hX : 0 < X) (hi : i ≤ Nat.log 2 X.sqrt)
    (u : ℝ) (hbig : Real.exp (2 * (u + 1)) ≤ (X : ℝ)) :
    let L : ℕ := 2 ^ (i + 1) - 1
    Real.exp u ≤ (X : ℝ) / L := by
  intro L
  have hpow : (2 : ℕ) ^ i ≤ X.sqrt :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans
      (Nat.pow_log_le_self 2 (Nat.sqrt_pos.mpr hX).ne')
  have hL0 : 0 < L := by
    change 0 < 2 ^ (i + 1) - 1
    rw [pow_succ]
    have hpow₀ : 0 < (2 : ℕ) ^ i := pow_pos (by decide) _
    omega
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL0
  have hL : (L : ℝ) ≤ 2 * (X.sqrt : ℝ) := by
    have hNat : L ≤ 2 * X.sqrt := by
      change 2 ^ (i + 1) - 1 ≤ 2 * X.sqrt
      rw [pow_succ]
      omega
    exact_mod_cast hNat
  have hLsq : (L : ℝ) ^ 2 ≤ 4 * (X : ℝ) := calc
    _ ≤ (2 * (X.sqrt : ℝ)) ^ 2 := pow_le_pow_left₀ hLpos.le hL _
    _ = 4 * (X.sqrt : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sqrt_le' X) (by norm_num)
  have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hXsq : 4 * Real.exp u ^ 2 ≤ (X : ℝ) := calc
    _ = (2 * Real.exp u) ^ 2 := by ring
    _ ≤ (Real.exp 1 * Real.exp u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h₂ (Real.exp_pos _).le) _
    _ = Real.exp (2 * (u + 1)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      apply congrArg Real.exp
      push_cast
      ring
    _ ≤ _ := hbig
  apply (le_div_iff₀ hLpos).mpr
  apply (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mp
  calc
    _ = (L : ℝ) ^ 2 * Real.exp u ^ 2 := by ring
    _ ≤ (4 * (X : ℝ)) * Real.exp u ^ 2 := mul_le_mul_of_nonneg_right hLsq (by positivity)
    _ = (X : ℝ) * (4 * Real.exp u ^ 2) := by ring
    _ ≤ (X : ℝ) ^ 2 := by
      rw [pow_two (X : ℝ)]
      exact mul_le_mul_of_nonneg_left hXsq (Nat.cast_nonneg _)

/-- The Type I quotient rows, clearing multipliers and density loss share
a budget polynomial in the input complexity and common factor budget. -/
def typeIVaughanLogBudget (s : ℕ) (p P : ℝ) : ℝ :=
  let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
  let b := (2 * P + Z + 1 + 2) ^ 7
  let n₀ := P * ((s + 1 : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)
  1 + ((P + 2) ^ 5 + P + 21 * p) + (b + 1) * (n₀ + 1) + n₀ + 2 * P + 2 * s * P

private theorem typeI_log_budget_arithmetic {b N P c loss t : ℝ}
    (hb : 0 ≤ b) (hN : 0 ≤ N) (hP : 0 ≤ P) (hc : 0 ≤ c) (hloss : 0 ≤ loss)
    (ht : t = 1 + loss + (b + 1) * (N + 1) + N + 2 * P + c) :
    1 ≤ t ∧ P ≤ t ∧ c ≤ t ∧ b + 1 ≤ t ∧
      (b + 1) * N + P ≤ t ∧ P + N + (b + 1) * N + P ≤ t ∧ loss ≤ t := by
  have hprod : 0 ≤ (b + 1) * N := by positivity
  simp only [ht]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hb, hN, hP, hc, hloss, hprod]

theorem typeI_vaughan_log_budget {s n l : ℕ} {p P : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hl : (l : ℝ) ≤ Real.exp P) :
    let Z := p + ((P + 1) + ((P + 1) + 2) ^ 7 + 2) ^ 9
    let B := ⌈Real.exp ((2 * P + Z + 1 + 2) ^ 7)⌉₊
    let N := n * (s + 1) * 2 ^ s
    let A := B ^ N
    let t := typeIVaughanLogBudget s p P
    1 ≤ t ∧ (n : ℝ) ≤ t ∧ (2 : ℝ) * s * n ≤ t ∧ (B : ℝ) ≤ Real.exp t ∧
      ((A * l : ℕ) : ℝ) ≤ Real.exp t ∧ (l : ℝ) * N * A * Real.exp P ≤ Real.exp t ∧
      Real.exp (-t) ≤ Real.exp (-((P + 2) ^ 5 + P + 21 * p)) := by
  intro Z B N A t
  let b := (2 * P + Z + 1 + 2) ^ 7
  let n₀ := P * ((s + 1 : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)
  let loss := (P + 2) ^ 5 + P + 21 * p
  have hb : 0 ≤ b := by
    dsimp [b, Z]
    positivity
  have hn₀ : 0 ≤ n₀ := by
    dsimp [n₀]
    positivity
  have hloss : 0 ≤ loss := by
    dsimp [loss]
    positivity
  have ht : t = 1 + loss + (b + 1) * (n₀ + 1) + n₀ + 2 * P + 2 * s * P := rfl
  have hN : (N : ℝ) ≤ n₀ := by
    dsimp [N, n₀]
    push_cast
    gcongr
  have hB : (B : ℝ) ≤ Real.exp (b + 1) := calc
    _ ≤ Real.exp b + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    _ ≤ 2 * Real.exp b := by linarith only [Real.one_le_exp hb]
    _ ≤ Real.exp (b + 1) := by
      rw [Real.exp_add, mul_comm (2 : ℝ)]
      exact mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
  have hA : (A : ℝ) ≤ Real.exp ((b + 1) * n₀) := calc
    _ ≤ Real.exp (b + 1) ^ N := by
      simp only [A, Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg B) hB _
    _ = Real.exp ((N : ℝ) * (b + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [mul_comm (b + 1)]
      exact mul_le_mul_of_nonneg_right hN (by positivity)
  have hNexp : (N : ℝ) ≤ Real.exp n₀ := hN.trans (by linarith only [Real.add_one_le_exp n₀])
  have hcard : (2 : ℝ) * s * n ≤ 2 * s * P := by gcongr
  obtain ⟨ht1, htP, htc, htb, htA, htError, htLoss⟩ := typeI_log_budget_arithmetic hb hn₀ hP
    (by positivity : 0 ≤ (2 : ℝ) * s * P) hloss ht
  have hAl : ((A * l : ℕ) : ℝ) ≤ Real.exp ((b + 1) * n₀ + P) := by
    rw [Nat.cast_mul, Real.exp_add]
    gcongr
  have hError : (l : ℝ) * N * A * Real.exp P ≤ Real.exp (P + n₀ + (b + 1) * n₀ + P) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    gcongr
  exact ⟨ht1, hn.trans htP, hcard.trans htc, hB.trans (Real.exp_le_exp.mpr htb),
    hAl.trans (Real.exp_le_exp.mpr htA), hError.trans (Real.exp_le_exp.mpr htError),
    Real.exp_le_exp.mpr (neg_le_neg htLoss)⟩

end PrimeUniformity

#print axioms PrimeUniformity.typeI_vaughan_cofactor_exp_lower
#print axioms PrimeUniformity.typeI_vaughan_log_budget
