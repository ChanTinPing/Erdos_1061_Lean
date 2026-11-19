module

public import PrimeUniformity.CramerPrimeBlocks
public import PrimeUniformity.Weights
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A polynomial bound for the Cramér normalization

The prime reciprocal blocks reduce a logarithm of the normalization
to the harmonic sum of the block indices. The result is polynomial in
the binary logarithm of the prime cutoff.
-/

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

theorem harmonic_sum_pow_two_le (N : ℕ) :
    (∑ j ∈ Finset.range ((2 : ℕ) ^ N + 1), (1 : ℝ) / (j : ℝ)) ≤ (N : ℝ) + 1 := by
  induction N with
  | zero =>
    have htwo : Finset.range 2 = {0, 1} := by decide
    norm_num [htwo]
  | succ N ih =>
    let D : ℕ := (2 : ℕ) ^ N
    have hD : 0 < D := pow_pos (by decide : (0 : ℕ) < 2) _
    have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hlen : (2 : ℕ) ^ (N + 1) + 1 = (D + 1) + D := by
      dsimp only [D]
      rw [pow_succ]
      omega
    have htail : (∑ j ∈ Finset.range D, (1 : ℝ) / ((D + 1 + j : ℕ) : ℝ)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range D, (1 : ℝ) / (D : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          exact one_div_le_one_div_of_le hDr (by exact_mod_cast (show D ≤ D + 1 + j by omega))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [hDr.ne']
    change (∑ j ∈ Finset.range ((2 : ℕ) ^ (N + 1) + 1), (1 : ℝ) / (j : ℝ)) ≤
      ((N + 1 : ℕ) : ℝ) + 1
    rw [hlen, Finset.sum_range_add]
    calc
      _ ≤ ((N : ℝ) + 1) + 1 := add_le_add ih htail
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]

private theorem mem_cramerPrimeSet_iff {p Q : ℕ} :
    p ∈ cramerPrimeSet Q ↔ p ≤ Q ∧ p.Prime := by
  simp only [cramerPrimeSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private theorem cramerPrimeSet_one_eq_empty : cramerPrimeSet 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hle, hprime⟩ := mem_cramerPrimeSet_iff.mp hp
  exact (by decide : ¬ 2 ≤ (1 : ℕ)) (hprime.two_le.trans hle)

private theorem cramerPrimeSet_pow_succ (n : ℕ) :
    cramerPrimeSet ((2 : ℕ) ^ (n + 1)) =
      cramerPrimeSet ((2 : ℕ) ^ n) ∪ dyadicPrimeBlock n := by
  ext p
  by_cases hp : p.Prime
  · simp only [Finset.mem_union, mem_cramerPrimeSet_iff, mem_dyadicPrimeBlock, hp,
      and_true, pow_succ, mul_two, two_mul]
    constructor
    · intro h
      by_cases hmid : p ≤ (2 : ℕ) ^ n
      · exact Or.inl hmid
      · exact Or.inr ⟨lt_of_not_ge hmid, h⟩
    · rintro (h | h)
      · exact h.trans (Nat.le_add_right _ _)
      · exact h.2
  · simp [mem_cramerPrimeSet_iff, mem_dyadicPrimeBlock, hp]

private theorem cramerPrimeSet_disjoint_block (n : ℕ) :
    Disjoint (cramerPrimeSet ((2 : ℕ) ^ n)) (dyadicPrimeBlock n) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge (mem_cramerPrimeSet_iff.mp hp).1) (mem_dyadicPrimeBlock.mp hq).1

private theorem sum_prime_reciprocals_pow_le (N : ℕ) :
    (∑ p ∈ cramerPrimeSet ((2 : ℕ) ^ N), (1 : ℝ) / (p : ℝ)) ≤
      1 / 2 + 2 * (∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ)) := by
  induction N with
  | zero => norm_num [cramerPrimeSet_one_eq_empty]
  | succ N ih =>
    rw [cramerPrimeSet_pow_succ, Finset.sum_union (cramerPrimeSet_disjoint_block N),
      Finset.sum_range_succ]
    by_cases hN : N = 0
    · subst N
      have hblock : dyadicPrimeBlock 0 = {2} := by decide
      norm_num [cramerPrimeSet_one_eq_empty, hblock]
    · have htail : (∑ p ∈ dyadicPrimeBlock N, (1 : ℝ) / (p : ℝ)) ≤
          2 * (1 / (N : ℝ)) := by
        calc
          _ ≤ 2 / (N : ℝ) := dyadicPrimeBlock_reciprocal_sum_le N (Nat.pos_of_ne_zero hN)
          _ = _ := by ring
      calc
        _ ≤ (1 / 2 + 2 * (∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ))) +
            2 * (1 / (N : ℝ)) := add_le_add ih htail
        _ = _ := by ring

theorem sum_cramerPrimeReciprocal_le_exp_index {Q N B : ℕ}
    (hQ : Q ≤ (2 : ℕ) ^ N) (hN : N ≤ (2 : ℕ) ^ B) :
    (∑ p ∈ cramerPrimeSet Q, (1 : ℝ) / (p : ℝ)) ≤ 1 / 2 + 2 * ((B : ℝ) + 1) := by
  have hsub : cramerPrimeSet Q ⊆ cramerPrimeSet ((2 : ℕ) ^ N) := by
    intro p hp
    obtain ⟨hle, hprime⟩ := mem_cramerPrimeSet_iff.mp hp
    exact mem_cramerPrimeSet_iff.mpr ⟨hle.trans hQ, hprime⟩
  have hsub' : Finset.range N ⊆ Finset.range ((2 : ℕ) ^ B + 1) := by
    intro n hn
    exact Finset.mem_range.mpr
      ((Finset.mem_range.mp hn).trans_le (hN.trans (Nat.le_succ _)))
  have hharm : (∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ)) ≤ (B : ℝ) + 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun _ _ _ => by positivity)).trans
      (harmonic_sum_pow_two_le B)
  calc
    _ ≤ ∑ p ∈ cramerPrimeSet ((2 : ℕ) ^ N), (1 : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / 2 + 2 * (∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ)) := sum_prime_reciprocals_pow_le N
    _ ≤ _ := by linarith only [hharm]

private theorem cramerLocalDenominator_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith only [hp2]
  exact sub_pos.mpr ((div_lt_iff₀ hp0).mpr (by linarith only [hp2]))

private theorem log_cramerLocalInv_le {p : ℕ} (hp : p.Prime) :
    Real.log ((1 - 1 / (p : ℝ))⁻¹) ≤ 2 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith only [hp2]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith only [hp2]
  have hd := cramerLocalDenominator_pos hp
  calc
    _ ≤ (1 - 1 / (p : ℝ))⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    _ = 1 / ((p : ℝ) - 1) := by field_simp [hp0.ne', hp1.ne', hd.ne'] <;> ring
    _ ≤ _ := (div_le_div_iff₀ hp1 hp0).mpr (by linarith only [hp2])

theorem cramerNormalization_positive (Q : ℕ) : 0 < cramerNormalization Q :=
  Finset.prod_pos fun _ hp => inv_pos.mpr (cramerLocalDenominator_pos (mem_cramerPrimeSet_iff.mp hp).2)

theorem cramerNormalization_le_exp_dyadic {Q N B : ℕ}
    (hQ : Q ≤ (2 : ℕ) ^ N) (hN : N ≤ (2 : ℕ) ^ B) :
    cramerNormalization Q ≤ Real.exp (5 + 4 * (B : ℝ)) := by
  have hlog : Real.log (cramerNormalization Q) ≤ 5 + 4 * (B : ℝ) := by
    unfold cramerNormalization
    rw [Real.log_prod (fun _ hp => (inv_pos.mpr
      (cramerLocalDenominator_pos (mem_cramerPrimeSet_iff.mp hp).2)).ne')]
    calc
      _ ≤ ∑ p ∈ cramerPrimeSet Q, (2 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum fun _ hp => log_cramerLocalInv_le (mem_cramerPrimeSet_iff.mp hp).2
      _ = 2 * (∑ p ∈ cramerPrimeSet Q, (1 : ℝ) / (p : ℝ)) := by
        rw [Finset.mul_sum]
        simp only [div_eq_mul_inv, one_mul]
      _ ≤ _ := by linarith only [sum_cramerPrimeReciprocal_le_exp_index hQ hN]
  exact (Real.exp_log (cramerNormalization_positive Q)).symm.le.trans (Real.exp_le_exp.mpr hlog)

private theorem exp_four_le_two_pow_eight : Real.exp 4 ≤ (2 : ℝ) ^ 8 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
  rw [Real.log_inv] at h
  have hh : (4 : ℝ) ≤ ((8 : ℕ) : ℝ) * Real.log 2 := by
    norm_num at h ⊢
    linarith only [h]
  calc
    _ ≤ Real.exp (((8 : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hh
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- For a cutoff bounded by a dyadic power, the normalization grows at
most polynomially in that power's exponent. -/
theorem cramerNormalization_le_poly_dyadic {Q N : ℕ} (hQ : Q ≤ (2 : ℕ) ^ N) :
    cramerNormalization Q ≤ Real.exp 5 * (2 * max (N : ℝ) 1) ^ 8 := by
  let M := max N 1
  let B := M.log2 + 1
  have hMge : 1 ≤ M := le_max_right _ _
  have hM : M ≠ 0 := (Nat.zero_lt_one.trans_le hMge).ne'
  have hN : N ≤ (2 : ℕ) ^ B := (le_max_left N 1).trans (Nat.lt_log2_self (n := M)).le
  have hB : (2 : ℕ) ^ B ≤ 2 * M := by
    calc
      _ = (2 : ℕ) ^ M.log2 * 2 := pow_succ _ _
      _ ≤ M * 2 := Nat.mul_le_mul_right _ (Nat.log2_self_le hM)
      _ = _ := Nat.mul_comm _ _
  have hBr : (2 : ℝ) ^ B ≤ 2 * (M : ℝ) := by exact_mod_cast hB
  have hMcast : (M : ℝ) = max (N : ℝ) 1 := by
    by_cases hz : N = 0
    · subst N
      norm_num [M]
    · have hpos : 1 ≤ N := Nat.pos_of_ne_zero hz
      have hpos' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpos
      simp only [M, max_eq_left hpos, max_eq_left hpos']
  calc
    _ ≤ Real.exp (5 + 4 * (B : ℝ)) := cramerNormalization_le_exp_dyadic hQ hN
    _ = Real.exp 5 * (Real.exp 4) ^ B := by
      rw [Real.exp_add, mul_comm (4 : ℝ) (B : ℝ), Real.exp_nat_mul]
    _ ≤ Real.exp 5 * ((2 : ℝ) ^ 8) ^ B :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le exp_four_le_two_pow_eight _)
        (Real.exp_pos _).le
    _ = Real.exp 5 * ((2 : ℝ) ^ B) ^ 8 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 8 B]
    _ ≤ Real.exp 5 * (2 * (M : ℝ)) ^ 8 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBr _) (Real.exp_pos _).le
    _ = _ := by rw [hMcast]

theorem abs_cramerWeight_le_poly_dyadic {Q N : ℕ} (hQ : Q ≤ (2 : ℕ) ^ N) (n : ℤ) :
    |cramerWeight Q n| ≤ Real.exp 5 * (2 * max (N : ℝ) 1) ^ 8 := by
  unfold cramerWeight
  split
  · rw [abs_of_pos (cramerNormalization_positive Q)]
    exact cramerNormalization_le_poly_dyadic hQ
  · simp only [abs_zero]
    positivity

private theorem reciprocal_step_product (n : ℕ) :
    (∏ j ∈ Finset.range n, ((j : ℝ) + 2) / ((j : ℝ) + 1)) = (n : ℝ) + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.cast_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn] <;> ring

/-- A coarse upper bound that suffices for the finite model sieve.
For transference one uses a stronger polylogarithmic estimate. -/
theorem cramerNormalization_le_cutoff {Q : ℕ} (hQ : 1 ≤ Q) :
    cramerNormalization Q ≤ (Q : ℝ) := by
  classical
  let P := cramerPrimeSet Q
  let f := fun j : ℕ => ((j : ℝ) + 2) / ((j : ℝ) + 1)
  have hP (p : ℕ) (hp : p ∈ P) : 2 ≤ p ∧ p ≤ Q := by
    have hprime := (mem_cramerPrimeSet_iff.mp hp).2
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    exact ⟨hprime.two_le, Nat.lt_succ_iff.mp hlt⟩
  have hinj : Set.InjOn (fun p : ℕ => p - 2) (P : Set ℕ) := by
    intro p hp q hq he
    have h₁ := (hP p hp).1
    have h₂ := (hP q hq).1
    change p - 2 = q - 2 at he
    omega
  have hsub : P.image (fun p => p - 2) ⊆ Finset.range (Q - 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have := hP p hp
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ P, f (p - 2) := by
      unfold cramerNormalization
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast ((mem_cramerPrimeSet_iff.mp hp).2).pos
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := (hP p hp).1; omega)
      have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) :=
        sub_pos.mpr ((div_lt_iff₀ hp0).mpr (by simpa using hp1))
      dsimp [f]
      rw [Nat.cast_sub (hP p hp).1]
      push_cast
      field_simp [hp0.ne', hpos.ne'] <;> ring
    _ = ∏ j ∈ P.image (fun p => p - 2), f j := by rw [Finset.prod_image hinj]
    _ ≤ ∏ j ∈ Finset.range (Q - 1), f j := by
      have hf (j : ℕ) : 1 ≤ f j := by
        dsimp [f]
        exact (le_div_iff₀ (by positivity)).mpr (by linarith)
      have hone (s : Finset ℕ) : 1 ≤ ∏ j ∈ s, f j := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert j s hj ih =>
          rw [Finset.prod_insert hj]
          exact one_le_mul_of_one_le_of_one_le (hf j) ih
      rw [← Finset.prod_sdiff hsub]
      exact le_mul_of_one_le_left (Finset.prod_nonneg fun j _ => zero_le_one.trans (hf j)) (hone _)
    _ = _ := by
      rw [show (∏ j ∈ Finset.range (Q - 1), f j) = ((Q - 1 : ℕ) : ℝ) + 1 from reciprocal_step_product _,
        Nat.cast_sub hQ, Nat.cast_one, sub_add_cancel]


end PrimeUniformity
