module

public import PrimeUniformity.WeylInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Classical Polynomial

/-- The natural numbers in the closed dyadic interval `[L/2, L]`. -/
def dyadicDilationInterval (L : ℕ) : Finset ℕ :=
  Finset.Ico ((L + 1) / 2) (L + 1)

/-- At the upper endpoint of a binary block, the recovery interval is
exactly the corresponding Vaughan dyadic range before clipping. -/
theorem dyadicDilationInterval_pow_sub_one (i : ℕ) :
    dyadicDilationInterval (2 ^ (i + 1) - 1) = Finset.Ico (2 ^ i) (2 ^ (i + 1)) := by
  have hp : 0 < (2 : ℕ) ^ (i + 1) := by positivity
  rw [dyadicDilationInterval, Nat.sub_add_cancel hp]
  congr 1
  rw [pow_succ]
  omega

theorem card_dyadicDilationInterval_pow_sub_one (i : ℕ) :
    (dyadicDilationInterval (2 ^ (i + 1) - 1)).card = 2 ^ i := by
  rw [dyadicDilationInterval_pow_sub_one, Nat.card_Ico, pow_succ]
  omega

/-- The Fourier detection cutoff can be chosen proportional to the inverse
density. -/
theorem exists_dilation_frequency_cutoff {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R : ℕ, 0 < R ∧ 16 ≤ ρ * (R : ℝ) ∧ (R : ℝ) ≤ 16 / ρ + 1 := by
  let t : ℝ := 16 / ρ
  have ht : 0 < t := div_pos (by norm_num) hρ
  let R := ⌈t⌉₊
  have hR : t ≤ (R : ℝ) := Nat.le_ceil _
  exact ⟨R, Nat.cast_pos.mp (ht.trans_le hR),
    by simpa only [mul_comm] using (div_le_iff₀ hρ).mp hR,
    (Nat.ceil_lt_add_one ht.le).le⟩

/-- Recover the original coefficients from a dense set of good dyadic
dilation pairs. The side length assumptions pay for both Fourier detection
and the separated interpolation nodes. -/
theorem recover_pair_dilation_dyadic
    (L R : ℕ) (hL : 0 < L)
    (p₀ p₁ : ℝ[X]) {k : ℕ} {ρ H X : ℝ}
    (hk : 0 < k) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X)
    (hRρ : 16 ≤ ρ * R)
    (hfreq : 16 * (R : ℝ) * H ≤ X / L)
    (hden : ((R * WeylInverse.leadingInverseBudget k R : ℕ) : ℝ) * H ≤ X / L)
    (hsize : let B := WeylInverse.leadingInverseBudget k R * 2 ^ k + 1
      8 * (2 * (B : ℝ) + 3) * (k + 1) ≤ ρ * L)
    (hdense : let T := dyadicDilationInterval L
      ρ * (T.card : ℝ) * (T.card : ℝ) ≤
        (((T ×ˢ T).filter (fun p : ℕ × ℕ => ∃ z : ℤ,
          |p₀.coeff k * (p.1 : ℝ) ^ k + p₁.coeff k * (p.2 : ℝ) ^ k - z| ≤
            H / (X / L) ^ k)).card : ℝ)) :
    let D := WeylInverse.leadingInverseBudget k R
    let B := D * 2 ^ k + 1
    let K := 8 * (2 * (B : ℝ) + 3) * (k + 1) / ρ
    let E := ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k *
      (k + 1) * K ^ k * H / X ^ k
    ∃ q : ℕ, 0 < q ∧ q ≤ (R * D) ^ 2 ∧ ∃ a b : ℤ,
      |(q : ℝ) * p₀.coeff k - a| ≤ E ∧ |(q : ℝ) * p₁.coeff k - b| ≤ E := by
  let start := (L + 1) / 2
  let len := L + 1 - start
  let T := dyadicDilationInterval L
  let D := WeylInverse.leadingInverseBudget k R
  let A := (D : ℝ) * 2 ^ k
  let B := D * 2 ^ k + 1
  have hlen : 0 < len := by dsimp [len, start]; omega
  have hstartlen : start + len = L + 1 := by dsimp [len, start]; omega
  have hT_eq : T = Finset.Ico start (start + len) := by
    rw [hstartlen]
    rfl
  have hT : T.Nonempty := by
    rw [hT_eq]
    exact ⟨start, Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_add_of_pos_right hlen⟩⟩
  have hTcard : T.card = len := by
    rw [hT_eq, Nat.card_Ico, Nat.add_sub_cancel_left]
  have hcard : (L : ℝ) ≤ 2 * (T.card : ℝ) := by
    rw [hTcard]
    exact_mod_cast (show L ≤ 2 * len by dsimp [len, start]; omega)
  have hinterval (n : ℕ) (hn : n ∈ T) : (n : ℝ) ∈ Set.Icc 0 (L : ℝ) := by
    have hn' : n < L + 1 := (Finset.mem_Ico.mp hn).2
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_of_lt_succ hn'⟩
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hR : 0 < R := by
    by_contra! hn
    norm_num [Nat.eq_zero_of_le_zero hn] at hRρ
  have hratio : 1 ≤ X / (L : ℝ) := (one_le_div hL').mpr hLX
  have hpow : X / (L : ℝ) ≤ (X / (L : ℝ)) ^ k := le_self_pow₀ hratio hk.ne'
  have hpowpos : 0 < (X / (L : ℝ)) ^ k := pow_pos (zero_lt_one.trans_le hratio) _
  have hfreq' : 2 * Real.pi * R * (H / (X / L) ^ k) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpowpos).mpr
    have hpi : 2 * Real.pi * R * H ≤ 8 * R * H := by
      calc
        _ ≤ 2 * (4 : ℝ) * R * H := by gcongr; exact Real.pi_le_four
        _ = _ := by ring
    nlinarith only [hfreq, hpow, hpi]
  have hden' : ((R * D : ℕ) : ℝ) * (H / (X / L) ^ k) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hpowpos).mpr (hden.trans hpow)
  have hsize' : 4 * (2 * (B : ℝ) + 3) * (k + 1) ≤ ρ * (T.card : ℝ) := by
    have hsize'' : 8 * (2 * (B : ℝ) + 3) * (k + 1) ≤ ρ * L := hsize
    have h := mul_le_mul_of_nonneg_left hcard hρ.le
    nlinarith only [hsize'', h]
  have hB : A + 1 ≤ (B : ℝ) := by
    simp [A, B]
  have hInv : MonomialPhaseInverse T k D ρ A (L : ℝ) := by
    rw [hT_eq]
    exact monomialPhaseInverse_Ico (c := 2) k start len R hk hlen hρ
      (by simpa only [mul_comm ρ (R : ℝ)] using hRρ) hL' (by simpa only [hTcard] using hcard)
  have hRec := recover_pair_dilation_at_ambient_scale T hT p₀ p₁ hk hR hL'
    (hL'.trans_le hLX) hρ hH (by norm_num : (0 : ℝ) < 2) hB hRρ hfreq' hden'
    hsize' hcard hinterval (by simpa only [coeff_pair_dilation] using hdense) hInv
  have hK : 4 * (2 * (B : ℝ) + 3) * (k + 1) * 2 / ρ =
      8 * (2 * (B : ℝ) + 3) * (k + 1) / ρ := by ring
  dsimp only at hRec ⊢
  rwa [hK] at hRec

/-- Recover a coefficient from a dense set of good dyadic dilations.
If the interval has too few points for interpolation, one good positive
dilation clears the denominator with a bound from the spacing threshold. -/
theorem recover_single_dilation_dyadic
    (L R : ℕ) (hL : 0 < L)
    (p : ℝ[X]) {k : ℕ} {ρ H X : ℝ}
    (hk : 0 < k) (hρ : 0 < ρ) (hH : 0 ≤ H) (hLX : (L : ℝ) ≤ X)
    (hRρ : 16 ≤ ρ * R)
    (hfreq : 16 * (R : ℝ) * H ≤ X / L)
    (hden : ((R * WeylInverse.leadingInverseBudget k R : ℕ) : ℝ) * H ≤ X / L)
    (hdense : let T := dyadicDilationInterval L
      ρ * (T.card : ℝ) ≤
        ((T.filter (fun n : ℕ => ∃ z : ℤ,
          |p.coeff k * (n : ℝ) ^ k - z| ≤ H / (X / L) ^ k)).card : ℝ)) :
    let D := WeylInverse.leadingInverseBudget k R
    let B := D * 2 ^ k + 1
    let K := 8 * (2 * (B : ℝ) + 3) * (k + 1) / ρ
    let C := ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k * (k + 1) * K ^ k
    ∃ q : ℕ, 0 < q ∧ q ≤ max ((R * D) ^ 2) (⌈K⌉₊ ^ k) ∧ ∃ a : ℤ,
      |(q : ℝ) * p.coeff k - a| ≤ max C (K ^ k) * H / X ^ k := by
  dsimp only
  let T := dyadicDilationInterval L
  let D := WeylInverse.leadingInverseBudget k R
  let B := D * 2 ^ k + 1
  let K := 8 * (2 * (B : ℝ) + 3) * (k + 1) / ρ
  let C := ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k * (k + 1) * K ^ k
  let good (n : ℕ) := ∃ z : ℤ, |p.coeff k * (n : ℝ) ^ k - z| ≤ H / (X / L) ^ k
  have hX : 0 < X := (Nat.cast_pos.mpr hL).trans_le hLX
  have herr (U : ℝ) (hU : U ≤ max C (K ^ k)) :
      U * H / X ^ k ≤ max C (K ^ k) * H / X ^ k :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hU hH) (pow_nonneg hX.le _)
  by_cases hsize : 8 * (2 * (B : ℝ) + 3) * (k + 1) ≤ ρ * L
  · have hpair :
        ρ * (T.card : ℝ) * (T.card : ℝ) ≤
          (((T ×ˢ T).filter (fun pair : ℕ × ℕ => ∃ z : ℤ,
            |p.coeff k * (pair.1 : ℝ) ^ k +
              (0 : ℝ[X]).coeff k * (pair.2 : ℝ) ^ k - z| ≤ H / (X / L) ^ k)).card : ℝ) := by
      simp only [Polynomial.coeff_zero, zero_mul, add_zero]
      change _ ≤ (((T ×ˢ T).filter (fun pair : ℕ × ℕ => good pair.1)).card : ℝ)
      rw [Finset.filter_product_left (s := T) (t := T) good, Finset.card_product, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hdense (Nat.cast_nonneg T.card)
    obtain ⟨q, hq, hqD, a, _, ha, _⟩ :=
      recover_pair_dilation_dyadic L R hL p 0 hk hρ hH hLX hRρ hfreq hden hsize hpair
    exact ⟨q, hq, hqD.trans (le_max_left _ _), a, ha.trans (herr C (le_max_left _ _))⟩
  · have hLK : (L : ℝ) ≤ K := by
      apply (le_div_iff₀ hρ).mpr
      simpa only [mul_comm (L : ℝ) ρ] using (lt_of_not_ge hsize).le
    have hLmem : L ∈ T := by
      apply Finset.mem_Ico.mpr
      omega
    have hTpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨L, hLmem⟩)
    have hgoodpos : 0 < ((T.filter good).card : ℝ) := (mul_pos hρ hTpos).trans_le hdense
    obtain ⟨n, hn⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hgoodpos)
    obtain ⟨hnT, hngood⟩ := Finset.mem_filter.mp hn
    have hnbox : (L + 1) / 2 ≤ n ∧ n < L + 1 := Finset.mem_Ico.mp hnT
    have hnpos : 0 < n := by omega
    have hnL : n ≤ L := by omega
    have hLceil : L ≤ ⌈K⌉₊ := by exact_mod_cast hLK.trans (Nat.le_ceil K)
    obtain ⟨a, ha⟩ := hngood
    refine ⟨n ^ k, pow_pos hnpos _, (Nat.pow_le_pow_left (hnL.trans hLceil) k).trans
      (le_max_right _ _), a, ?_⟩
    rw [Nat.cast_pow, mul_comm ((n : ℝ) ^ k)]
    calc
      _ ≤ H / (X / (L : ℝ)) ^ k := ha
      _ = (L : ℝ) ^ k * H / X ^ k := by rw [div_pow, div_div_eq_mul_div]; ring
      _ ≤ K ^ k * H / X ^ k :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg L) hLK k) hH)
          (pow_nonneg hX.le _)
      _ ≤ max C (K ^ k) * H / X ^ k := herr _ (le_max_right _ _)

end PrimeUniformity
