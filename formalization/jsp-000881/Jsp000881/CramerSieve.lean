module

public import PrimeUniformity.IndependentSieve
public import Jsp000881.CRTIntersection
import all Jsp000881.CRTIntersection
public import Jsp000881.Bonferroni
public import Jsp000881.LatticeArea
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Squarefree

public section

namespace Jsp000881

open scoped BigOperators

export PrimeUniformity (independentTruncation independentTruncation_ge_product_sub_tail)

private noncomputable def boxIntersectionError (J : Finset ℕ) (len₁ len₂ : ℤ) : ℝ :=
  let D := (∏ p ∈ J, p)
  ((len₁ : ℝ) + (len₂ : ℝ)) * (D : ℝ) + (D : ℝ) ^ 2

noncomputable def boxSieveError (P : Finset ℕ) (len₁ len₂ : ℤ) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), ∑ J ∈ P.powersetCard j, boxIntersectionError J len₁ len₂

/-- Truncation of the model count with an explicit sum of all CRT errors. -/
theorem rectangleSieveLowerBound (θ : PlaneIndex) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (start₁ len₁ start₂ len₂ : ℤ) (h₁ : 0 ≤ len₁) (h₂ : 0 ≤ len₂) (L : ℕ) (hL : Odd L) :
    let X := (interval start₁ len₁).product (interval start₂ len₂)
    let bad := fun (p : ℕ) (nm : ℤ × ℤ) => ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ nm).coord i
    (len₁ : ℝ) * (len₂ : ℝ) * independentTruncation P (localBadDensity θ) L -
        boxSieveError P len₁ len₂ L ≤ survivingWeight P X bad (fun _ => 1) := by
  classical
  let X := (interval start₁ len₁).product (interval start₂ len₂)
  let bad := fun (p : ℕ) (nm : ℤ × ℤ) => ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ nm).coord i
  let area := (len₁ : ℝ) * (len₂ : ℝ)
  change area * independentTruncation P (localBadDensity θ) L -
    boxSieveError P len₁ len₂ L ≤ survivingWeight P X bad (fun _ => 1)
  let main := fun J : Finset ℕ => area * (∏ p ∈ J, localBadDensity θ p)
  let obs := fun J : Finset ℕ => intersectionWeight J X bad (fun _ => 1)
  have hpoint (J : Finset ℕ) (hJ : J ⊆ P) :
      |obs J - main J| ≤ boxIntersectionError J len₁ len₂ := by
    have hobs : obs J = ((badIntersection θ J start₁ len₁ start₂ len₂).card : ℝ) := by
      unfold obs intersectionWeight
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      apply congrArg (fun R : Finset (ℤ × ℤ) => (R.card : ℝ))
      ext nm
      simp only [badIntersection, Finset.mem_filter, X, bad]
    rw [hobs]
    exact badIntersection_discrepancy θ J (fun p hp => hP p (hJ hp)) start₁ len₁ start₂ len₂ h₁ h₂
  let E := fun j : ℕ => ∑ J ∈ P.powersetCard j, boxIntersectionError J len₁ len₂
  let D := fun j : ℕ => ∑ J ∈ P.powersetCard j, (obs J - main J)
  have hper (j : ℕ) : |D j| ≤ E j := by
    calc
      _ ≤ ∑ J ∈ P.powersetCard j, |obs J - main J| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun J hJ => hpoint J (Finset.mem_powersetCard.mp hJ).1
  have hdiff : truncation P X bad (fun _ => 1) L - area * independentTruncation P (localBadDensity θ) L =
      ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j * D j := by
    unfold truncation independentTruncation
    rw [Finset.mul_sum (Finset.range (L + 1)) _ area, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (-1 : ℝ) ^ j * (∑ J ∈ P.powersetCard j, obs J) -
      area * ((-1 : ℝ) ^ j * (∑ J ∈ P.powersetCard j, ∏ p ∈ J, localBadDensity θ p)) =
      (-1 : ℝ) ^ j * D j
    have hm : area * (∑ J ∈ P.powersetCard j, ∏ p ∈ J, localBadDensity θ p) =
        ∑ J ∈ P.powersetCard j, main J := Finset.mul_sum _ _ _
    calc
      _ = (-1 : ℝ) ^ j * ((∑ J ∈ P.powersetCard j, obs J) -
          area * (∑ J ∈ P.powersetCard j, ∏ p ∈ J, localBadDensity θ p)) := by ring
      _ = _ := by rw [hm, ← Finset.sum_sub_distrib] <;> rfl
  have habs : |truncation P X bad (fun _ => 1) L - area * independentTruncation P (localBadDensity θ) L| ≤
      boxSieveError P len₁ len₂ L := by
    rw [hdiff]
    calc
      _ ≤ ∑ j ∈ Finset.range (L + 1), |(-1 : ℝ) ^ j * D j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
        simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hper j
  have hleft := (abs_le.mp habs).1
  have hsurv := (bonferroni P X bad (fun _ => 1) (by intros; norm_num) L hL).1
  linarith only [hleft, hsurv]

/-- Distinct subsets of the sieved primes produce distinct moduli, all at
most `Q^L`. This bounds the total CRT error without a binomial coefficient. -/
theorem boxSieveError_le {P : Finset ℕ} {Q L : ℕ} (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    boxSieveError P a b L ≤
      ((a : ℝ) + (b : ℝ)) * ((Q ^ L : ℕ) : ℝ) ^ 2 + ((Q ^ L : ℕ) : ℝ) ^ 3 := by
  classical
  let S := P.powerset.filter fun J => J.card ≤ L
  let B : ℕ := Q ^ L
  let E := ((a : ℝ) + (b : ℝ)) * (B : ℝ) + (B : ℝ) ^ 2
  let modulus := fun J : Finset ℕ => ∏ p ∈ J, p
  have hpJ (J : Finset ℕ) (hJ : J ⊆ P) (hL : J.card ≤ L) :
      0 < modulus J ∧ modulus J ≤ B := by
    refine ⟨Finset.prod_pos (fun p hp => (hP p (hJ hp)).1.pos), ?_⟩
    exact (Finset.prod_le_pow_card J id Q (fun p hp => (hP p (hJ hp)).2)).trans
      (pow_right_mono₀ hQ hL)
  have hScard : S.card ≤ B := by
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
          Nat.primeFactors_prod (fun p hp => (hP p (hKP hp)).1)] using
            congrArg Nat.primeFactors he
    simpa [Nat.card_Icc] using hcard
  have hsum : S.card = ∑ j ∈ Finset.range (L + 1), (P.powersetCard j).card := by
    have hf : ∀ J ∈ S, J.card ∈ Finset.range (L + 1) := by
      intro J hJ
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hJ).2)
    rw [Finset.card_eq_sum_card_fiberwise hf]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ext J
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.symm ▸ hj'⟩, h.2⟩⟩
  have hA : (0 : ℝ) ≤ (a : ℝ) + (b : ℝ) := add_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  unfold boxSieveError
  calc
    _ ≤ ∑ j ∈ Finset.range (L + 1), ∑ _J ∈ P.powersetCard j, E := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro J hJ
      obtain ⟨hsub, hj'⟩ := Finset.mem_powersetCard.mp hJ
      have hD := (hpJ J hsub (hj'.symm ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
      have hDr : (modulus J : ℝ) ≤ (B : ℝ) := by exact_mod_cast hD
      exact add_le_add (mul_le_mul_of_nonneg_left hDr hA)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hDr 2)
    _ = (S.card : ℝ) * E := by simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul,
      hsum, Nat.cast_sum]
    _ ≤ (B : ℝ) * E := mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) hE
    _ = _ := by dsimp [B, E]; ring

end Jsp000881
