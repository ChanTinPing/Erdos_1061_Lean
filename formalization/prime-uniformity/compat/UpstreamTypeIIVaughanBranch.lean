import UpstreamTypeIIVaughanFactors

namespace PrimeUniformity

open Filter OAI.Erdos3
open scoped TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- The actual Vaughan Type II alternative yields the native orbit
factorization with polynomial recovery and complexity bounds. -/
theorem native_prime_prepared_typeII_factor_recovery (k : ℕ) :
    NativePrimePreparedTypeIIFactorRecovery k := by
  let s := k + 1
  obtain ⟨C, D, _, _, hFactors⟩ := exists_typeII_native_factors_of_vaughan s (by omega)
  let Xp : Polynomial ℕ := Polynomial.X
  let B := (111 * Xp + Polynomial.C C) ^ C
  let N := B + 132 * Xp
  let Z := Xp + (Xp + 2) ^ 2 + (B + Polynomial.C s) + (B + Polynomial.C s * (121 * Xp + 11 * Xp))
  let U := (Z + (Z + 4) ^ 5 + (Z + 2) ^ 4 + 2) ^ 4
  let G := 3 * Z + ((Z + 1 + (Z + 3) ^ 7 + 2) ^ 9 + Z + 4) ^ 4 + (Z + U + 2) ^ 4
  let A := (Z + U + (G + 3) ^ 7 + 2) ^ 4
  let T := 1 + 21 * Z + 2 * Polynomial.C s * Z +
    (3 * Z * (Z + 1) * (Z + 2) + (Z + 2) ^ 5 + Z + 153 * Z) + (A + 1) +
    (2 * Z + (Z * (Polynomial.C s + 1) * Polynomial.C (2 ^ s)) * ((G + 3) ^ 7 + 2))
  let R := Polynomial.C D * T ^ 2
  let I := G + Z + U
  let V := I + (I + (I + 3) ^ 7 + 2) ^ 4 + 1
  let P₀ := N + Polynomial.C D * T + ((R + 2) ^ 48 + (R + 2) ^ 24 + R + 1)
  let Q₀ := Xp + (V + V * ((V + 2) ^ 7 + V)) +
    Polynomial.C s * (R + 2) ^ 36 + ((R + 2) ^ 18 + R)
  refine ⟨P₀, Q₀, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with X hX
  intro r _ p hp hcost W ω hω hnorm η hη hVert _ _ hq A₀ F₀ hlarge
  obtain ⟨i, _, j, _, hlarge⟩ := hlarge
  let t := typeIIProjectionBudget s (typeIIVaughanGeometryBudget s C p)
  let J := separationBudget ((D : ℝ) * t ^ 2)
  have hPeval : P₀.eval₂ (Nat.castRingHom ℝ) p =
      ((111 * p + C) ^ C + 132 * p) + (D : ℝ) * t + J := by
    simp [P₀, N, R, T, A, G, U, Z, B, Xp, t, J, typeIIProjectionBudget, typeIIVaughanGeometryBudget,
      separationBudget, typeIIPairedAxisRowLogBudget, typeIIPairedGeneratorBudget,
      refiltrationCoordinateBudget, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
  have hQeval : Q₀.eval₂ (Nat.castRingHom ℝ) p = typeIIVaughanFactorBudget s C D p := by
    simp [Q₀, V, I, R, T, A, G, U, Z, B, Xp, typeIIVaughanFactorBudget, typeIIProjectionBudget,
      typeIIVaughanGeometryBudget, typeIIPairedAxisRowLogBudget, typeIIPairedGeneratorBudget,
      refiltrationCoordinateBudget, adaptedMarkedMapHeightBudget, preimageBasisBudget, sparseGeneratorBudget,
      Polynomial.eval₂_pow]
  rw [hPeval] at hcost
  have hp₀ : 0 ≤ p := by have := (le_max_left _ _).trans hp; linarith
  have hraw : 0 ≤ (111 * p + C) ^ C + 132 * p := by positivity
  have hlog₄ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog₂ : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hz : 0 ≤ typeIIVaughanGeometryBudget s C p := by unfold typeIIVaughanGeometryBudget; positivity
  have ht : 0 ≤ t := by
    have hG := refiltrationCoordinateBudget_nonneg hz
    unfold t typeIIProjectionBudget typeIIPairedAxisRowLogBudget typeIIPairedGeneratorBudget
      adaptedMarkedMapHeightBudget
    positivity
  have hdt : 0 ≤ (D : ℝ) * t := by positivity
  have hJ : 0 ≤ J := separationBudget_nonneg (by positivity)
  have hsep : Real.exp J ≤ X := by
    have hlog : J ≤ Real.log (X : ℝ) := by linarith only [hcost, hraw, hlog₄, hJ, hdt]
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (Nat.cast_pos.mpr (by omega)))
  rw [hQeval]
  exact hFactors W ω hω hnorm η hη hVert hX hp hq.le
    (by linarith only [hcost, hdt, hJ, hlog₂])
    (by linarith only [hcost, hraw, hJ]) hsep i j hlarge

/-- The prepared Type II branch closes with an actual correlated
lower-rank native test. -/
theorem native_prime_prepared_typeII_branch (k : ℕ) : NativePrimePreparedTypeIIBranch k :=
  native_prime_prepared_typeII_branch_of_factors (native_prime_prepared_typeII_factor_recovery k)

end PrimeUniformity

#print axioms PrimeUniformity.native_prime_prepared_typeII_factor_recovery
#print axioms PrimeUniformity.native_prime_prepared_typeII_branch
