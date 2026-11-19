import UpstreamTypeIIPairedGenerators

namespace PrimeUniformity

open OAI.Erdos3

/-- A common logarithmic budget for Type II density, row heights, and all
of the integer multipliers entering the paired Weyl estimate. -/
noncomputable def typeIIProjectionBudget (s : ℕ) (z : ℝ) : ℝ :=
  1 + 21 * z + 2 * (s : ℝ) * z +
    (3 * z * (z + 1) * (z + 2) + (z + 2) ^ 5 + z + 153 * z) +
    (typeIIPairedAxisRowLogBudget z + 1) +
    (2 * z + (z * ((s : ℝ) + 1) * 2 ^ s) * ((typeIIPairedGeneratorBudget z + 3) ^ 7 + 2))

theorem typeIIProjectionBudget_bounds {s d B l : ℕ} {z P p B₀ : ℝ}
    (hz : 0 ≤ z) (hp : 0 ≤ p) (hpz : p ≤ z)
    (hB₀ : 0 ≤ B₀) (hB₀z : B₀ ≤ z) (hP : 0 ≤ P) (hPz : P ≤ z)
    (hd : (d : ℝ) ≤ z)
    (hB : (B : ℝ) ≤ Real.exp ((typeIIPairedGeneratorBudget z + 3) ^ 7 + 1))
    (hl : (l : ℝ) ≤ Real.exp P) :
    let N := d * (s + 1) * 2 ^ s
    let t := typeIIProjectionBudget s z
    1 ≤ t ∧ z ≤ t ∧ 21 * p ≤ t ∧ 2 * (s : ℝ) * d ≤ t ∧
    3 * (d : ℝ) * ((d : ℝ) + 1) * (B₀ + 2) + ((P + 2) ^ 5 + P) + 153 * p ≤ t ∧
    (⌈Real.exp (typeIIPairedAxisRowLogBudget z)⌉₊ : ℝ) ≤ Real.exp t ∧
    (↑(B ^ N * l) : ℝ) ≤ Real.exp t ∧
    (l : ℝ) * (N : ℝ) * (B ^ N : ℕ) * Real.exp P ≤ Real.exp t := by
  intro N t
  let Q := typeIIPairedGeneratorBudget z
  let K := (Q + 3) ^ 7 + 1
  let M := z * ((s : ℝ) + 1) * 2 ^ s
  have hN : (N : ℝ) ≤ M := by
    push_cast [N, M]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity)
  have hQ : 0 ≤ Q := by
    have hcost := refiltrationCoordinateBudget_nonneg hz
    dsimp only [Q, typeIIPairedGeneratorBudget]
    positivity
  have hLog : 0 ≤ typeIIPairedAxisRowLogBudget z := by
    unfold typeIIPairedAxisRowLogBudget adaptedMarkedMapHeightBudget
    change 0 ≤ (z + (z + (z + 4) ^ 5 + (z + 2) ^ 4 + 2) ^ 4 + (Q + 3) ^ 7 + 2) ^ 4
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hsz : 0 ≤ 2 * (s : ℝ) * z := by positivity
  let D := 3 * z * (z + 1) * (z + 2) + (z + 2) ^ 5 + z + 153 * z
  let E := 2 * z + M * (K + 1)
  have hD₀ : 0 ≤ D := by dsimp only [D]; positivity
  have hE₀ : 0 ≤ E := by dsimp only [E]; positivity
  have ht : t = 1 + 21 * z + 2 * (s : ℝ) * z + D + (typeIIPairedAxisRowLogBudget z + 1) + E := by
    dsimp only [t, typeIIProjectionBudget, D, E, M, K, Q]
    ring
  have hD : 3 * (d : ℝ) * ((d : ℝ) + 1) * (B₀ + 2) + ((P + 2) ^ 5 + P) + 153 * p ≤ D := by
    calc
      _ ≤ 3 * z * (z + 1) * (z + 2) + ((z + 2) ^ 5 + z) + 153 * z := by gcongr
      _ = _ := by dsimp only [D]; ring
  have hcomp : (N : ℝ) * K + (N : ℝ) + 2 * P ≤ E := by
    have hKN := mul_le_mul_of_nonneg_right hN (show 0 ≤ K + 1 by positivity)
    dsimp only [E]
    linarith only [hKN, hPz]
  have hPow : (↑(B ^ N) : ℝ) ≤ Real.exp ((N : ℝ) * K) := by
    rw [Nat.cast_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
  have hNat : (N : ℝ) ≤ Real.exp (N : ℝ) := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hEt : E ≤ t := by rw [ht]; linarith
  refine ⟨by rw [ht]; linarith, by rw [ht]; linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hpz (by norm_num)).trans (by rw [ht]; linarith)
  · exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans (by rw [ht]; linarith)
  · exact hD.trans (by rw [ht]; linarith)
  · exact (ceil_exp_le_exp_add_one hLog).trans (Real.exp_le_exp.mpr (by rw [ht]; linarith))
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((N : ℝ) * K) * Real.exp P :=
        mul_le_mul hPow hl (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((N : ℝ) * K + P) := (Real.exp_add _ _).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ((by
        linarith [Nat.cast_nonneg (α := ℝ) N] : (N : ℝ) * K + P ≤ (N : ℝ) * K + N + 2 * P).trans
          (hcomp.trans hEt))
  · calc
      _ ≤ Real.exp P * Real.exp (N : ℝ) * Real.exp ((N : ℝ) * K) * Real.exp P := by gcongr
      _ = Real.exp ((N : ℝ) * K + N + 2 * P) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (hcomp.trans hEt)

end PrimeUniformity

#print axioms PrimeUniformity.typeIIProjectionBudget_bounds
