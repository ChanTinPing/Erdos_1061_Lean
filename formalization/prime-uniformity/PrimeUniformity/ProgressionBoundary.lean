module

public import PrimeUniformity.ProgressionComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

private theorem prime_dvd_nonunit_residue {q : ℕ} (hq : 0 < q) (a : ZMod q) (ha : ¬IsUnit a) :
    ∃ p : ℕ, p.Prime ∧ p ∣ q ∧ ∀ n : ℤ, (n : ZMod q) = a → (p : ℤ) ∣ n := by
  let : NeZero q := ⟨hq.ne'⟩
  have ha' : ¬ a.val.Coprime q := by
    intro hc
    exact ha (by simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val q).mpr hc)
  obtain ⟨p, hp, hpa, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp ha'
  refine ⟨p, hp, hpq, ?_⟩
  intro n hn
  let f := ZMod.castHom hpq (ZMod p)
  have hf := congrArg f hn
  rw [map_intCast, ← ZMod.natCast_zmod_val a, map_natCast,
    (ZMod.natCast_eq_zero_iff a.val p).mpr hpa] at hf
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hf

private theorem residueVonMangoldt_le_of_prime_dvd {X q p : ℕ} (hX : 1 ≤ X) (hp : p.Prime)
    (a : ZMod q) (hd : ∀ n : ℤ, (n : ZMod q) = a → (p : ℤ) ∣ n) :
    residueVonMangoldt a X ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) * Real.log (X : ℝ) := by
  classical
  let S := (Finset.Icc 1 X).filter (fun n : ℕ => (n : ZMod q) = a)
  let T := S.filter (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)
  have hterm (n : ℕ) (hn : n ∈ T) : ∃ k ≤ Nat.log 2 X, p ^ k = n := by
    obtain ⟨hnS, hn₀⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnX, hna⟩ := Finset.mem_filter.mp hnS
    have hh := isPrimePow_nat_iff_bounded_log n
    obtain ⟨k, hk, _, r, _, hr, hprime⟩ :=
      hh.mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn₀)
    have hpd : p ∣ n := by
      exact_mod_cast hd (n : ℤ) (by simpa only [Int.cast_natCast] using hna)
    have hpr : p = r := Nat.prime_eq_prime_of_dvd_pow hp hprime (hr ▸ hpd)
    exact ⟨k, hk.trans (Nat.log_mono_right (Finset.mem_Icc.mp hnX).2), by rwa [hpr, eq_comm]⟩
  have hcard : T.card ≤ Nat.log 2 X + 1 := by
    have hsub : T ⊆ (Finset.range (Nat.log 2 X + 1)).image (fun k => p ^ k) := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := hterm n hn
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩
    exact (Finset.card_le_card hsub).trans (by
      simpa using Finset.card_image_le (s := Finset.range (Nat.log 2 X + 1))
        (f := fun k => p ^ k))
  have hsum : (∑ n ∈ T, ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by by_cases hn : ArithmeticFunction.vonMangoldt n = 0 <;> simp [hn])
  rw [residueVonMangoldt, ← hsum]
  calc
    _ ≤ ∑ _ ∈ T, Real.log (X : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hnX.1) (by exact_mod_cast hnX.2))
    _ = (T.card : ℝ) * Real.log (X : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.log_nonneg (by exact_mod_cast hX))

/-- On a nonunit class at a sieved modulus, the Cramér weight vanishes
and ordinary von Mangoldt sees only powers of one prime. -/
theorem prime_cramer_nonunit_progression_le {X Q q U V : ℕ}
    (hX : 1 ≤ X) (hUV : U ≤ V) (hVX : V ≤ X) (hq : 0 < q) (hqQ : q ≤ Q)
    (a : ZMod q) (ha : ¬IsUnit a) :
    |∑ n ∈ residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a,
      (vonMangoldtWeight n - cramerWeight Q n)| ≤
        ((Nat.log 2 X + 1 : ℕ) : ℝ) * Real.log (X : ℝ) := by
  obtain ⟨p, hp, hpq, hpd⟩ := prime_dvd_nonunit_residue hq a ha
  let S := residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a
  have hpQ : p ∈ cramerPrimeSet Q := by
    have h := (Nat.le_of_dvd hq hpq).trans hqQ
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h), hp⟩
  have hz (n : ℤ) (hn : n ∈ S) : cramerWeight Q n = 0 := by
    have hcast := (Finset.mem_filter.mp hn).2
    have hbad : ¬ (∀ r ∈ cramerPrimeSet Q, ¬(r : ℤ) ∣ n) :=
      fun h => h p hpQ (hpd n hcast)
    simp only [cramerWeight, if_neg hbad]
  have heq : (∑ n ∈ S, (vonMangoldtWeight n - cramerWeight Q n)) =
      ∑ n ∈ S, vonMangoldtWeight n := Finset.sum_congr rfl (fun n hn => by rw [hz n hn, sub_zero])
  have hpos (n : ℤ) : 0 ≤ vonMangoldtWeight n := ArithmeticFunction.vonMangoldt_nonneg
  have hsub : S ⊆ residueSlice 1 (X : ℤ) a := by
    intro n hn
    simp only [S, residueSlice, interval, Finset.mem_filter, Finset.mem_Ico, Int.natCast_sub hUV] at hn ⊢
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  rw [heq, abs_of_nonneg (Finset.sum_nonneg fun n _ => hpos n)]
  calc
    _ ≤ ∑ n ∈ residueSlice 1 (X : ℤ) a, vonMangoldtWeight n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hpos n)
    _ = residueVonMangoldt a X := (residueVonMangoldt_eq_interval a X).symm
    _ ≤ _ := residueVonMangoldt_le_of_prime_dvd hX hp a hpd

private theorem abs_vonMangoldtWeight_le_log {X : ℕ} {n : ℤ}
    (hn : 1 ≤ n) (hnX : n ≤ (X : ℤ)) :
    |vonMangoldtWeight n| ≤ Real.log (X : ℝ) := by
  rw [vonMangoldtWeight, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < n.toNat by omega))
      (by exact_mod_cast (show n.toNat ≤ X by omega)))

/-- A prime theorem with the upstream modulus range supplies the comparison
over every progression contained in the ambient integer interval. -/
theorem uniform_prime_cramer_progressions (h : UniformPrimePrefixEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ U V : ℕ, U ≤ V → V ≤ X → ∀ (q : ℕ), 0 < q → ∀ a : ZMod q,
        |∑ n ∈ residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a,
          (vonMangoldtWeight n - cramerWeight (strictPrimeUniformityCutoff X) n)| ≤
          C * (X : ℝ) * Real.exp (-c * Real.log (X : ℝ) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hreduced⟩ := uniform_prime_cramer_reduced_progressions h
  obtain ⟨B, hB, hbound⟩ := eventually_abs_cramerWeight_le_log_pow
  let c := min c₁ 1
  let D := 1 / Real.log 2 + 1
  let C := max C₁ (max D (2 * (1 + B)))
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  have hc : 0 < c := lt_min hc₁ one_pos
  refine ⟨c, C, hc, hC, ?_⟩
  have hLog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSmall : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hLog
  filter_upwards [hreduced, hbound, eventually_ge_atTop (1 : ℕ),
    hLog.eventually_ge_atTop 1, hSmall.eventually_ge_atTop 2,
    eventually_log_pow_le_exp_log_rpow 8 (c := 1 / 20) (by norm_num)]
    with X hreduced hbound hX hLog hSmall hpoly
  intro U V hUV hVX q hq a
  let L := Real.log (X : ℝ)
  let s := L ^ (1 / 20 : ℝ)
  let t := L ^ (1 / 10 : ℝ)
  let Q := strictPrimeUniformityCutoff X
  let R := residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a
  change 1 ≤ L at hLog
  change 2 ≤ s at hSmall
  change L ^ (8 : ℕ) ≤ Real.exp s at hpoly
  have hL : 0 ≤ L := zero_le_one.trans hLog
  have hx : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
  have h_expL : Real.exp L = (X : ℝ) :=
    Real.exp_log (by exact_mod_cast (Nat.zero_lt_one.trans_le hX))
  have hst : s ≤ t := Real.rpow_le_rpow_of_exponent_le hLog (by norm_num)
  have htL : t ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLog (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hs₂ : s ^ (2 : ℕ) = t := by
    dsimp only [s, t]
    rw [← Real.rpow_mul_natCast hL]
    norm_num
  have htwos : 2 * s ≤ t := by
    rw [← hs₂, pow_two]
    exact mul_le_mul_of_nonneg_right hSmall (by linarith)
  have hlogPow (k : ℕ) (hk : k ≤ 8) : L ^ k ≤ L ^ (8 : ℕ) := pow_right_mono₀ hLog hk
  have hweaken : Real.exp (-s) ≤ Real.exp (-c * s) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right c₁ (1 : ℝ)) (show 0 ≤ s by linarith)
    linarith
  by_cases hqQ : q ≤ Q
  · by_cases ha : IsUnit a
    · refine (hreduced U V hUV hVX q hq hqQ a ha).trans ?_
      have he : Real.exp (-c₁ * t) ≤ Real.exp (-c * s) := by
        apply Real.exp_le_exp.mpr
        have hs₀ : 0 ≤ s := by linarith
        have h := mul_le_mul (min_le_left c₁ (1 : ℝ)) hst hs₀ hc₁.le
        linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hx) he
        (Real.exp_pos _).le (by positivity)
    · refine (prime_cramer_nonunit_progression_le hX hUV hVX hq hqQ a ha).trans ?_
      have hbin : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ D * L := by
        push_cast
        calc
          _ ≤ L / Real.log 2 + L := add_le_add (log_nat_cast_le_log_div_log_two hX) hLog
          _ = _ := by dsimp [D]; ring
      have hsc : Real.exp s ≤ (X : ℝ) * Real.exp (-s) := by
        rw [← h_expL, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc
        _ ≤ (D * L) * L := mul_le_mul_of_nonneg_right hbin hL
        _ = D * L ^ (2 : ℕ) := by ring
        _ ≤ D * Real.exp s := mul_le_mul_of_nonneg_left ((hlogPow 2 (by decide)).trans hpoly) hD.le
        _ ≤ D * (X : ℝ) * Real.exp (-s) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hsc hD.le
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_right ((le_max_left D (2 * (1 + B))).trans (le_max_right C₁ _)) hx)
          hweaken (Real.exp_pos _).le (by positivity)
  · have hqExp : Real.exp t ≤ (q : ℝ) := by
      have hceil : ⌈Real.exp t⌉₊ ≤ q := by
        change ¬q ≤ ⌈Real.exp t⌉₊ - 1 at hqQ
        omega
      exact (Nat.le_ceil (Real.exp t)).trans (by exact_mod_cast hceil)
    have hXExp : Real.exp t ≤ (X : ℝ) :=
      (Real.exp_le_exp.mpr htL).trans_eq h_expL
    have hcard : (R.card : ℝ) ≤ 2 * (X : ℝ) / Real.exp t := by
      have hlen : ((V - U : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast (Nat.sub_le V U).trans hVX
      have hratio : 1 ≤ (X : ℝ) / Real.exp t := (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa using hXExp)
      calc
        _ ≤ (((V - U : ℕ) : ℤ) : ℝ) / (q : ℝ) + 1 :=
          card_residueSlice_le _ _ hq (by positivity) a
        _ ≤ (X : ℝ) / Real.exp t + 1 := by
          rw [Int.cast_natCast]
          exact add_le_add (div_le_div₀ (by positivity) hlen (Real.exp_pos _) hqExp) le_rfl
        _ ≤ 2 * (X : ℝ) / Real.exp t := by rw [mul_div_assoc]; linarith
    have hweight (n : ℤ) (hn : n ∈ R) :
        |vonMangoldtWeight n - cramerWeight Q n| ≤ (1 + B) * Real.exp s := by
      have hcoord := hn
      simp only [R, residueSlice, interval, Finset.mem_filter, Finset.mem_Ico, Int.natCast_sub hUV] at hcoord
      have hprime := abs_vonMangoldtWeight_le_log (X := X) (by omega : 1 ≤ n) (by omega)
      have hCram := hbound Q (strictPrimeUniformityCutoff_le X) n
      calc
        _ ≤ |vonMangoldtWeight n| + |cramerWeight Q n| := abs_sub _ _
        _ ≤ L + B * L ^ (8 : ℕ) := add_le_add hprime hCram
        _ ≤ (1 + B) * L ^ (8 : ℕ) := by
          rw [add_mul, one_mul]
          exact add_le_add (by simpa only [pow_one] using hlogPow 1 (by decide)) le_rfl
        _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)
    change |∑ n ∈ R, (vonMangoldtWeight n - cramerWeight Q n)| ≤ _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have htailExp : Real.exp (s - t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ ∑ _ ∈ R, (1 + B) * Real.exp s := Finset.sum_le_sum hweight
      _ = (R.card : ℝ) * ((1 + B) * Real.exp s) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (X : ℝ) / Real.exp t) * ((1 + B) * Real.exp s) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (1 + B)) * (X : ℝ) * Real.exp (s - t) := by
        rw [Real.exp_sub]
        ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right ((le_max_right D (2 * (1 + B))).trans (le_max_right C₁ _)) hx)
        (htailExp.trans hweaken) (Real.exp_pos _).le (by positivity)

end PrimeUniformity
