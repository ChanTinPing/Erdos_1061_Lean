module

public import PrimeUniformity.CramerNormalization
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The squarefree product of the primes removed by the Cramér sieve. -/
noncomputable def cramerPrimeProduct (Q : ℕ) : ℕ :=
  ∏ p ∈ cramerPrimeSet Q, p

private theorem prime_of_mem_cramerPrimeSet {Q p : ℕ} (hp : p ∈ cramerPrimeSet Q) :
    p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem cramerPrimeProduct_pos (Q : ℕ) : 0 < cramerPrimeProduct Q :=
  Finset.prod_pos fun _ hp => (prime_of_mem_cramerPrimeSet hp).pos

private theorem cramerPrimeProduct_squarefree (Q : ℕ) : Squarefree (cramerPrimeProduct Q) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (prime_of_mem_cramerPrimeSet hp) (prime_of_mem_cramerPrimeSet hr)).mpr hpr)
  · exact fun _ hp => (prime_of_mem_cramerPrimeSet hp).squarefree

/-- Exact finite divisor expansion of the Cramér weight on natural inputs. -/
theorem cramerWeight_eq_divisor_sum (Q n : ℕ) :
    cramerWeight Q n =
      cramerNormalization Q * ∑ d ∈ (cramerPrimeProduct Q).divisors,
        if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  let P := cramerPrimeProduct Q
  let M : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  have hP : P ≠ 0 := (cramerPrimeProduct_pos Q).ne'
  have hgood : (∀ p ∈ cramerPrimeSet Q, ¬(p : ℤ) ∣ (n : ℤ)) ↔ P.gcd n = 1 := by
    change _ ↔ P.Coprime n
    simp only [Int.natCast_dvd_natCast, P, cramerPrimeProduct, Nat.coprime_prod_left_iff]
    exact forall₂_congr fun p hp => (prime_of_mem_cramerPrimeSet hp).coprime_iff_not_dvd.symm
  have hset : P.divisors.filter (fun d => d ∣ n) = (P.gcd n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, Nat.gcd_ne_zero_left hP⟩,
      fun h => ⟨⟨h.1.1, hP⟩, h.1.2⟩⟩
  have hM : (M * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hsum : (∑ d ∈ (P.gcd n).divisors, M d) = if P.gcd n = 1 then (1 : ℝ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, hM, ArithmeticFunction.one_apply]
  unfold cramerWeight
  change (if ∀ p ∈ cramerPrimeSet Q, ¬(p : ℤ) ∣ (n : ℤ) then cramerNormalization Q else 0) =
    cramerNormalization Q * ∑ d ∈ P.divisors, if d ∣ n then M d else 0
  rw [← Finset.sum_filter, hset, hsum]
  simp [hgood, mul_ite]

/-- Keep only the divisor terms whose modulus is at most D. -/
noncomputable def cramerTruncatedWeight (Q D n : ℕ) : ℝ :=
  cramerNormalization Q * ∑ d ∈ (cramerPrimeProduct Q).divisors.filter (· ≤ D),
    if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0

/-- Coefficient of the modulus in the truncated Type I sum. -/
noncomputable def cramerTypeICoefficient (Q d : ℕ) : ℝ :=
  if d ∣ cramerPrimeProduct Q then
    cramerNormalization Q * (ArithmeticFunction.moebius d : ℝ)
  else 0

theorem abs_cramerTypeICoefficient_le (Q d : ℕ) :
    |cramerTypeICoefficient Q d| ≤ cramerNormalization Q := by
  have hQ := (cramerNormalization_positive Q).le
  by_cases hd : d ∣ cramerPrimeProduct Q
  · have hM : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    simpa [cramerTypeICoefficient, hd, abs_mul, abs_of_nonneg hQ] using
      mul_le_mul_of_nonneg_left hM hQ
  · simpa [cramerTypeICoefficient, hd] using hQ

/-- The truncated weight is a Type I sum over positive moduli at most D. -/
theorem cramerTruncatedWeight_eq_typeI (Q D n : ℕ) :
    cramerTruncatedWeight Q D n =
      ∑ d ∈ Finset.Icc 1 D, if d ∣ n then cramerTypeICoefficient Q d else 0 := by
  have hset : (cramerPrimeProduct Q).divisors.filter (· ≤ D) =
      (Finset.Icc 1 D).filter (· ∣ cramerPrimeProduct Q) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    exact ⟨fun ⟨⟨hd, _⟩, hb⟩ =>
      ⟨⟨Nat.pos_of_dvd_of_pos hd (cramerPrimeProduct_pos Q), hb⟩, hd⟩,
      fun ⟨⟨_, hb⟩, hd⟩ => ⟨⟨hd, (cramerPrimeProduct_pos Q).ne'⟩, hb⟩⟩
  rw [cramerTruncatedWeight, hset, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hp : d ∣ cramerPrimeProduct Q <;> by_cases hn : d ∣ n <;>
    simp [cramerTypeICoefficient, hp, hn]

private theorem cramerWeight_sub_truncated_eq_tail (Q D n : ℕ) :
    cramerWeight Q n - cramerTruncatedWeight Q D n =
      cramerNormalization Q * ∑ d ∈ (cramerPrimeProduct Q).divisors.filter (D < ·),
        if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  let S := (cramerPrimeProduct Q).divisors
  let f (d : ℕ) : ℝ := if d ∣ n then ArithmeticFunction.moebius d else 0
  have h := Finset.sum_filter_add_sum_filter_not S (· ≤ D) f
  simp only [not_le] at h
  rw [cramerWeight_eq_divisor_sum, cramerTruncatedWeight]
  change cramerNormalization Q * (∑ d ∈ S, f d) -
    cramerNormalization Q * (∑ d ∈ S.filter (· ≤ D), f d) =
      cramerNormalization Q * ∑ d ∈ S.filter (D < ·), f d
  rw [← h]
  ring

/-- Pointwise error charged to the discarded divisors of the input. -/
theorem abs_cramerWeight_sub_truncated_le (Q D n : ℕ) :
    |cramerWeight Q n - cramerTruncatedWeight Q D n| ≤
      cramerNormalization Q * ∑ d ∈ (cramerPrimeProduct Q).divisors.filter (D < ·),
        if d ∣ n then (1 : ℝ) else 0 := by
  rw [cramerWeight_sub_truncated_eq_tail, abs_mul,
    abs_of_nonneg (cramerNormalization_positive Q).le]
  apply mul_le_mul_of_nonneg_left _ (cramerNormalization_positive Q).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro d _
  by_cases hn : d ∣ n
  · have hM : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    simpa only [if_pos hn] using hM
  · simp [hn]

/-- The finite L¹ truncation error is bounded by the reciprocal mass of
the discarded moduli. -/
theorem sum_abs_cramerWeight_sub_truncated_le (Q D X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n|) ≤
      cramerNormalization Q * ((X : ℝ) *
        ∑ d ∈ (cramerPrimeProduct Q).divisors.filter (D < ·), (d : ℝ)⁻¹) := by
  let S := (cramerPrimeProduct Q).divisors.filter (D < ·)
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 X, cramerNormalization Q *
        ∑ d ∈ S, if d ∣ n then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun n _ => abs_cramerWeight_sub_truncated_le Q D n
    _ = cramerNormalization Q * ∑ d ∈ S, ((X / d : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (cramerNormalization_positive Q).le
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun d _ => by
        simpa only [div_eq_mul_inv] using (Nat.cast_div_le (α := ℝ) (m := X) (n := d))

private theorem cramerPrimeProduct_divisor_sum_rpow (Q : ℕ) (s : ℝ) :
    (∑ d ∈ (cramerPrimeProduct Q).divisors, (d : ℝ) ^ s) =
      ∏ p ∈ cramerPrimeSet Q, (1 + (p : ℝ) ^ s) := by
  let P := cramerPrimeSet Q
  let M := cramerPrimeProduct Q
  have hpr : M.primeFactors = P :=
    Nat.primeFactors_prod fun _ hp => prime_of_mem_cramerPrimeSet hp
  have hsq : Squarefree M := cramerPrimeProduct_squarefree Q
  have hprod (d : ℕ) (hd : d ∈ M.divisors) : (∏ p ∈ d.primeFactors, p) = d :=
    Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    apply Finset.mem_powerset.mpr
    change d.primeFactors ⊆ P
    rw [← hpr]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hsq.ne_zero
  · intro d hd e he hde
    rw [← hprod d hd, ← hprod e he, hde]
  · intro J hJ
    have hsub : J ⊆ P := Finset.mem_powerset.mp hJ
    refine ⟨∏ p ∈ J, p, Nat.mem_divisors.mpr ⟨?_, hsq.ne_zero⟩, ?_⟩
    · exact Finset.prod_dvd_prod_of_subset J P id hsub
    · exact Nat.primeFactors_prod fun _ hp => prime_of_mem_cramerPrimeSet (hsub hp)
  · intro d hd
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) s, ← Nat.cast_prod, hprod d hd]

/-- Rankin's bound for the reciprocal mass of divisors above the truncation. -/
theorem cramerDivisorTail_le_rankin (Q D : ℕ) (hD : 0 < D) (s : ℝ) (hs : 0 ≤ s) :
    (∑ d ∈ (cramerPrimeProduct Q).divisors.filter (D < ·), (d : ℝ)⁻¹) ≤
      ((D : ℝ) ^ s)⁻¹ * ∏ p ∈ cramerPrimeSet Q, (1 + (p : ℝ) ^ (s - 1)) := by
  let S := (cramerPrimeProduct Q).divisors.filter (D < ·)
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDs := Real.rpow_pos_of_pos hD' s
  change (∑ d ∈ S, (d : ℝ)⁻¹) ≤ _
  rw [← cramerPrimeProduct_divisor_sum_rpow]
  calc
    _ ≤ ∑ d ∈ S, ((D : ℝ) ^ s)⁻¹ * (d : ℝ) ^ (s - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hDd : (D : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hd).2.le
      have hb := Real.rpow_le_rpow hD'.le hDd hs
      rw [Real.rpow_sub hd', Real.rpow_one]
      calc
        _ = ((D : ℝ) ^ s)⁻¹ * ((D : ℝ) ^ s / (d : ℝ)) := by
          rw [← mul_div_assoc, inv_mul_cancel₀ hDs.ne', one_div]
        _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hd'.le)
          (inv_nonneg.mpr hDs.le)
    _ = ((D : ℝ) ^ s)⁻¹ * ∑ d ∈ S, (d : ℝ) ^ (s - 1) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hDs.le)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end PrimeUniformity
