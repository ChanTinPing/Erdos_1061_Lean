module

public import PrimeUniformity.CramerNormalization
public import PrimeUniformity.IndependentSieve
public import PrimeUniformity.ResidueIntervals
public import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- Sieve primes that can eliminate points in a reduced residue class modulo q. -/
noncomputable def cramerAPPrimes (Q q : ℕ) : Finset ℕ :=
  cramerPrimeSet Q \ q.primeFactors

private theorem cramerPrimeSet_mem {Q p : ℕ} :
    p ∈ cramerPrimeSet Q ↔ p ≤ Q ∧ p.Prime := by
  simp only [cramerPrimeSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

private theorem cramerAPPrimes_mem {Q q p : ℕ} (hq : 0 < q) :
    p ∈ cramerAPPrimes Q q ↔ (p ≤ Q ∧ p.Prime) ∧ ¬p ∣ q := by
  rw [cramerAPPrimes, Finset.mem_sdiff, cramerPrimeSet_mem, Nat.mem_primeFactors_of_ne_zero hq.ne']
  exact ⟨fun ⟨hp, hm⟩ => ⟨hp, fun hd => hm ⟨hp.2, hd⟩⟩,
    fun ⟨hp, hm⟩ => ⟨hp, fun h => hm h.2⟩⟩

private theorem primeProduct_int_dvd_iff (J : Finset ℕ) (hJ : ∀ p ∈ J, p.Prime) (n : ℤ) :
    (((∏ p ∈ J, p : ℕ) : ℤ) ∣ n) ↔ ∀ p ∈ J, (p : ℤ) ∣ n := by
  simp only [Int.natCast_dvd]
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    by_cases hn : n.natAbs = 0
    · rw [hn]
      exact dvd_zero _
    · have hsub : J ⊆ n.natAbs.primeFactors := fun p hp =>
        (hJ p hp).mem_primeFactors (h p hp) hn
      exact (Finset.prod_dvd_prod_of_subset J n.natAbs.primeFactors id hsub).trans
        (Nat.prod_primeFactors_dvd n.natAbs)

private theorem cramerAP_intersection_discrepancy (Q q : ℕ) (hq : 0 < q)
    (start len : ℤ) (hlen : 0 ≤ len) (a : ZMod q)
    (J : Finset ℕ) (hJ : J ⊆ cramerAPPrimes Q q) :
    |intersectionWeight J (residueSlice start len a) (fun p n => (p : ℤ) ∣ n) (fun _ => 1) -
      ((len : ℝ) / (q : ℝ)) * (∏ p ∈ J, (1 : ℝ) / (p : ℝ))| ≤ 1 := by
  classical
  let D : ℕ := ∏ p ∈ J, p
  have hprime (p : ℕ) (hp : p ∈ J) : p.Prime :=
    ((cramerAPPrimes_mem hq).mp (hJ hp)).1.2
  have hcop : q.Coprime D := Nat.coprime_prod_right_iff.mpr fun p hp =>
    ((hprime p hp).coprime_iff_not_dvd.mpr ((cramerAPPrimes_mem hq).mp (hJ hp)).2).symm
  have hD : 0 < D := Finset.prod_pos fun p hp => (hprime p hp).pos
  let e : ZMod (q * D) ≃+* ZMod q × ZMod D := ZMod.chineseRemainder hcop
  let r : ZMod (q * D) := e.symm (a, 0)
  have hcrt (n : ℤ) : (n : ZMod (q * D)) = r ↔ (n : ZMod q) = a ∧ (n : ZMod D) = 0 := by
    have hcast : e (n : ZMod (q * D)) = ((n : ZMod q), (n : ZMod D)) := by
      rw [map_intCast]
      rfl
    calc
      _ ↔ e (n : ZMod (q * D)) = e r := e.injective.eq_iff.symm
      _ ↔ _ := by
        rw [hcast, show e r = (a, 0) from e.apply_symm_apply (a, 0)]
        simp only [Prod.mk.injEq]
  have hcount :
      intersectionWeight J (residueSlice start len a)
        (fun p n => (p : ℤ) ∣ n) (fun _ => 1) = ((residueSlice start len r).card : ℝ) := by
    simp only [intersectionWeight, Finset.sum_const, nsmul_eq_mul, mul_one]
    apply congrArg (fun S : Finset ℤ => (S.card : ℝ))
    ext n
    have hdiv : (n : ZMod D) = 0 ↔ ∀ p ∈ J, (p : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n D).trans (primeProduct_int_dvd_iff J hprime n)
    simp only [residueSlice, Finset.mem_filter, hcrt, hdiv, and_assoc]
  have hprod : (∏ p ∈ J, (1 : ℝ) / (p : ℝ)) = (D : ℝ)⁻¹ := by
    simp only [D, one_div, Finset.prod_inv_distrib, Nat.cast_prod]
  rw [hcount, hprod]
  simpa only [Nat.cast_mul, div_eq_mul_inv, mul_inv, mul_assoc] using
    residueSlice_discrepancy start len (Nat.mul_pos hq hD) hlen r

private theorem reduced_int_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    {a : ZMod q} (ha : IsUnit a) {n : ℤ} (hn : (n : ZMod q) = a) :
    ¬(p : ℤ) ∣ n := by
  let : Fact p.Prime := ⟨hp⟩
  let f : ZMod q →+* ZMod p := ZMod.castHom hpq (ZMod p)
  have hunit : IsUnit (n : ZMod p) := by
    have hu : IsUnit (n : ZMod q) := hn ▸ ha
    simpa only [map_intCast] using hu.map f
  intro hd
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr hd] at hunit
  exact not_isUnit_zero hunit

private theorem cramerAP_sum_eq_survivingWeight (Q q : ℕ) (hq : 0 < q)
    (start len : ℤ) (a : ZMod q) (ha : IsUnit a) :
    (∑ n ∈ residueSlice start len a, cramerWeight Q n) =
      cramerNormalization Q * survivingWeight (cramerAPPrimes Q q)
        (residueSlice start len a) (fun p n => (p : ℤ) ∣ n) (fun _ => 1) := by
  classical
  simp only [survivingWeight, Finset.mul_sum, mul_one]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold cramerWeight
  have hn' : (n : ZMod q) = a := (Finset.mem_filter.mp hn).2
  have he : (∀ p ∈ cramerPrimeSet Q, ¬(p : ℤ) ∣ n) ↔
      ∀ p ∈ cramerAPPrimes Q q, ¬(p : ℤ) ∣ n := by
    constructor
    · intro h p hp
      exact h p (Finset.mem_sdiff.mp hp).1
    · intro h p hp
      by_cases hdiv : p ∣ q
      · exact reduced_int_not_dvd (cramerPrimeSet_mem.mp hp).2 hdiv ha hn'
      · exact h p ((cramerAPPrimes_mem hq).mpr ⟨cramerPrimeSet_mem.mp hp, hdiv⟩)
  simp [he]

private theorem totient_eq_product_real (q : ℕ) :
    (q.totient : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
    one_div] using h

private theorem cramerAP_normalized_density (Q q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q) (len : ℤ) :
    cramerNormalization Q * (((len : ℝ) / (q : ℝ)) *
      ∏ p ∈ cramerAPPrimes Q q, (1 - 1 / (p : ℝ))) = (len : ℝ) / (q.totient : ℝ) := by
  have hsub : q.primeFactors ⊆ cramerPrimeSet Q := fun p hp =>
    cramerPrimeSet_mem.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hqQ, Nat.prime_of_mem_primeFactors hp⟩
  let U : ℝ := ∏ p ∈ cramerAPPrimes Q q, (1 - 1 / (p : ℝ))
  let V : ℝ := ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))
  have hfactor (p : ℕ) (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
    apply sub_pos.mpr
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact (div_lt_iff₀ (zero_lt_one.trans h)).mpr (by simpa only [one_mul] using h)
  have hU : U ≠ 0 := (Finset.prod_pos (fun p hp =>
    hfactor p ((cramerAPPrimes_mem hq).mp hp).1.2)).ne'
  have hV : V ≠ 0 := (Finset.prod_pos (fun p hp =>
    hfactor p (Nat.prime_of_mem_primeFactors hp))).ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [cramerNormalization, Finset.prod_inv_distrib, ← Finset.prod_sdiff hsub,
    totient_eq_product_real]
  change (U * V)⁻¹ * (((len : ℝ) / (q : ℝ)) * U) = (len : ℝ) / ((q : ℝ) * V)
  field_simp [hU, hV, hq']

/-- Finite Cramér progression estimate, with a count of the subsets used by
the larger Bonferroni truncation and the factorial tail. -/
theorem cramerAP_error_le (Q q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q)
    (start len : ℤ) (hlen : 0 ≤ len) (a : ZMod q) (ha : IsUnit a)
    (L : ℕ) (hL : Odd L) :
    |(∑ n ∈ residueSlice start len a, cramerWeight Q n) - (len : ℝ) / (q.totient : ℝ)| ≤
      cramerNormalization Q *
        ((∑ j ∈ Finset.range (L + 2), (((cramerAPPrimes Q q).powersetCard j).card : ℝ)) +
          ((len : ℝ) / (q : ℝ)) *
            ((∑ p ∈ cramerAPPrimes Q q, (1 : ℝ) / (p : ℝ)) ^ (L + 1) /
              ((L + 1).factorial : ℝ))) := by
  let P := cramerAPPrimes Q q
  let M := (len : ℝ) / (q : ℝ)
  have hM : 0 ≤ M := div_nonneg (by exact_mod_cast hlen) (Nat.cast_nonneg _)
  have hg (p : ℕ) (hp : p ∈ P) : 0 ≤ (1 : ℝ) / (p : ℝ) ∧ (1 : ℝ) / (p : ℝ) ≤ 1 := by
    have h : (1 : ℝ) ≤ p := by exact_mod_cast ((cramerAPPrimes_mem hq).mp hp).1.2.one_lt.le
    exact ⟨by positivity, (div_le_iff₀ (zero_lt_one.trans_le h)).mpr (by simpa only [one_mul] using h)⟩
  have h := survivingWeight_error P (residueSlice start len a)
    (fun p n => (p : ℤ) ∣ n) (fun _ => 1) (fun _ _ => zero_le_one)
    (fun p => (1 : ℝ) / (p : ℝ)) hg hM
    (fun _ => 1) (fun _ _ => zero_le_one) L hL
    (fun J hJ => cramerAP_intersection_discrepancy Q q hq start len hlen a J hJ)
  rw [cramerAP_sum_eq_survivingWeight Q q hq start len a ha,
    ← cramerAP_normalized_density Q q hq hqQ len, ← mul_sub, abs_mul,
    abs_of_nonneg (cramerNormalization_positive Q).le]
  apply mul_le_mul_of_nonneg_left _ (cramerNormalization_positive Q).le
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

/-- Distinct sieve subsets give distinct positive products at most Q^(L+1). -/
theorem cramerAP_truncation_count_le (Q q L : ℕ) (hQ : 1 ≤ Q) :
    (∑ j ∈ Finset.range (L + 2), (((cramerAPPrimes Q q).powersetCard j).card : ℝ)) ≤
      (Q : ℝ) ^ (L + 1) := by
  classical
  let P := cramerAPPrimes Q q
  let S := P.powerset.filter fun J => J.card ≤ L + 1
  let B : ℕ := Q ^ (L + 1)
  let modulus (J : Finset ℕ) := ∏ p ∈ J, p
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Q :=
    (cramerPrimeSet_mem.mp (Finset.mem_sdiff.mp hp).1).symm
  have hpJ (J : Finset ℕ) (hJ : J ⊆ P) (hL : J.card ≤ L + 1) :
      1 ≤ modulus J ∧ modulus J ≤ B := by
    refine ⟨Finset.prod_pos (fun p hp => (hP p (hJ hp)).1.pos), ?_⟩
    exact (Finset.prod_le_pow_card J id Q (fun p hp => (hP p (hJ hp)).2)).trans
      (pow_right_mono₀ hQ hL)
  have hcard : S.card ≤ (Finset.Icc 1 B).card := by
    apply Finset.card_le_card_of_injOn modulus
    · intro J hJ
      have hj := Finset.mem_filter.mp hJ
      obtain ⟨hlo, hhi⟩ := hpJ J (Finset.mem_powerset.mp hj.1) hj.2
      exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
    · intro J hJ K hK he
      have hJP := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ).1
      have hKP := Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
      simpa only [modulus, Nat.primeFactors_prod (fun p hp => (hP p (hJP hp)).1),
        Nat.primeFactors_prod (fun p hp => (hP p (hKP hp)).1)] using congrArg Nat.primeFactors he
  have hsum : S.card = ∑ j ∈ Finset.range (L + 2), (P.powersetCard j).card := by
    have hf : ∀ J ∈ S, J.card ∈ Finset.range (L + 2) := fun J hJ =>
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hJ).2)
    rw [Finset.card_eq_sum_card_fiberwise hf]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ext J
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.symm ▸ hj'⟩, h.2⟩⟩
  have hbound : S.card ≤ B := by simpa [Nat.card_Icc] using hcard
  have hbound' : (∑ j ∈ Finset.range (L + 2), (P.powersetCard j).card) ≤ Q ^ (L + 1) := by
    rw [← hsum]
    exact hbound
  rw [← Nat.cast_sum]
  exact_mod_cast hbound'

end PrimeUniformity
