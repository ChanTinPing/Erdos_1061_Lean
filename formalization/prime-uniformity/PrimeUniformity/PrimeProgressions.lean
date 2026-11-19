module

public import PrimeUniformity.PrimePowers
public import PrimeUniformity.ResidueIntervals
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- Ordinary von Mangoldt mass up to `Y` in a residue class modulo `q`. -/
noncomputable def residueVonMangoldt {q : ℕ} (a : ZMod q) (Y : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod q) = a),
    ArithmeticFunction.vonMangoldt n

private theorem residueVonMangoldt_nonneg {q : ℕ} (a : ZMod q) (Y : ℕ) :
    0 ≤ residueVonMangoldt a Y := by
  unfold residueVonMangoldt
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

private theorem residueVonMangoldt_le {q X Y : ℕ} (a : ZMod q)
    (hX : 1 ≤ X) (hY : Y ≤ X) :
    residueVonMangoldt a Y ≤ (Y : ℝ) * Real.log (X : ℝ) := by
  classical
  unfold residueVonMangoldt
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  calc
    _ ≤ ∑ _ ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod q) = a), Real.log (X : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn₁, hnY⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
      · exact_mod_cast hn₁
      · exact_mod_cast hnY.trans hY
    _ ≤ ∑ _ ∈ Finset.Icc 1 Y, Real.log (X : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hlog)
    _ = _ := by simp [Nat.card_Icc, nsmul_eq_mul]

/-- A single-prefix estimate of the strength of the large-modulus
Siegel–Walfisz theorem. -/
def UniformPrimePrefixEstimate : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ Y : ℕ in atTop,
    ∀ (q : ℕ), 0 < q → ∀ a : ZMod q, IsUnit a →
      (q : ℝ) ≤ Real.exp (Real.log (Y : ℝ) ^ (1 / 3 : ℝ)) →
      |residueVonMangoldt a Y - (Y : ℝ) / (q.totient : ℝ)| ≤
        C * (Y : ℝ) * Real.exp (-c * Real.log (Y : ℝ) ^ (1 / 3 : ℝ))

/-- The ordinary prefix equals the sum on the zero-based range with the
residue-class indicator. The term at zero vanishes. -/
theorem residueVonMangoldt_eq_range {q : ℕ} (a : ZMod q) (Y : ℕ) :
    residueVonMangoldt a Y = ∑ n ∈ Finset.range (Y + 1),
      if (n : ZMod q) = a then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  rw [residueVonMangoldt, Finset.sum_filter]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have hzero : n = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at hn hnot
      omega
    subst n
    simp

/-- Adapt a real-height prime prefix estimate in the range convention to the
natural-height estimate used by the progression comparison. -/
theorem UniformPrimePrefixEstimate.of_real_range
    (h : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ Y : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], ∀ a : ZMod q, IsUnit a →
      (q : ℝ) ≤ Real.exp (Real.log Y ^ (1 / 3 : ℝ)) →
      |(∑ n ∈ Finset.range (⌊Y⌋₊ + 1),
          if (n : ZMod q) = a then ArithmeticFunction.vonMangoldt n else 0) -
          Y / (q.totient : ℝ)| ≤
        C * Y * Real.exp (-c * Real.log Y ^ (1 / 3 : ℝ))) :
    UniformPrimePrefixEstimate := by
  obtain ⟨c, C, hc, hC, h⟩ := h
  have hnat : Tendsto (fun Y : ℕ => (Y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hnat.eventually h] with Y hY
  intro q hq a ha hqY
  letI : NeZero q := ⟨hq.ne'⟩
  rw [residueVonMangoldt_eq_range]
  simpa only [Nat.floor_natCast] using hY q a ha hqY

/-- The single-prefix bound supplies a uniform error at all shorter
prefixes of the ambient interval, at the moduli needed by the prime comparison. -/
theorem uniform_primePrefix_of_large_modulus (h : UniformPrimePrefixEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ Y ≤ X, ∀ (q : ℕ), 0 < q → ∀ a : ZMod q, IsUnit a →
        (q : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)) →
        |residueVonMangoldt a Y - (Y : ℝ) / (q.totient : ℝ)| ≤
          C * (X : ℝ) * Real.exp (-c * Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, C, hc, hC, h⟩ := h
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp h
  let c₀ := min c (1 / 4)
  let D := max C 2
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have hc₁ : c₀ ≤ 1 / 4 := min_le_right _ _
  have hc₂ : c₀ ≤ c := min_le_left _ _
  have hD : 0 < D := lt_of_lt_of_le hC (le_max_left _ _)
  refine ⟨c₀, D, hc₀, hD, ?_⟩
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlin := ht.eventually
    ((isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : 0 < (1 / 4 : ℝ))).bound one_pos)
  filter_upwards [eventually_ge_atTop (Y₀ ^ 2), eventually_ge_atTop (1 : ℕ),
    ht.eventually_ge_atTop 4, hlin] with X hXY₀ hX hlarge hlin
  intro Y hY q hq a ha hqX
  let L := Real.log (X : ℝ)
  change (4 : ℝ) ≤ L at hlarge
  have hL : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 4).trans hlarge
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hrate : c₀ * L ^ (1 / 10 : ℝ) ≤ L / 4 := by
    have hpow : L ^ (1 / 10 : ℝ) ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (show 1 ≤ L by linarith) (by norm_num : (1 / 10 : ℝ) ≤ 1)
    calc
      _ ≤ (1 / 4 : ℝ) * L :=
        mul_le_mul hc₁ hpow (Real.rpow_nonneg hL _) (by norm_num)
      _ = _ := by ring
  by_cases hshort : Y ^ 2 ≤ X
  · have hYn : (Y : ℝ) ≤ Real.sqrt X :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast hshort)
    have hYpos : 0 ≤ (Y : ℝ) := by positivity
    have hφ : 1 ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    have hmain : (Y : ℝ) / (q.totient : ℝ) ≤ (Y : ℝ) := by
      exact div_le_self hYpos hφ
    have hmass := residueVonMangoldt_le a hX hY
    have hnorm : L ≤ Real.exp ((1 / 4 : ℝ) * L) := by
      change ‖L ^ (1 : ℕ)‖ ≤ 1 * ‖Real.exp ((1 / 4 : ℝ) * L)‖ at hlin
      simpa only [pow_one, one_mul, Real.norm_of_nonneg hL,
        Real.norm_of_nonneg (Real.exp_pos _).le] using hlin
    have hnorm' : L + 1 ≤ 2 * Real.exp ((1 / 4 : ℝ) * L) := by
      have h := Real.one_le_exp (by positivity : 0 ≤ (1 / 4 : ℝ) * L)
      linarith
    have hsqrt : Real.sqrt X = Real.exp ((1 / 2 : ℝ) * L) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXpos, mul_comm]
    calc
      _ ≤ residueVonMangoldt a Y + (Y : ℝ) / (q.totient : ℝ) := by
        simpa only [abs_of_nonneg (residueVonMangoldt_nonneg a Y),
          abs_of_nonneg (div_nonneg hYpos (Nat.cast_nonneg q.totient))] using
          (abs_sub _ _ : |residueVonMangoldt a Y - (Y : ℝ) / (q.totient : ℝ)| ≤
            |residueVonMangoldt a Y| + |(Y : ℝ) / (q.totient : ℝ)|)
      _ ≤ (Y : ℝ) * (L + 1) := by linarith only [hmass, hmain]
      _ ≤ Real.sqrt X * (2 * Real.exp ((1 / 4 : ℝ) * L)) :=
        mul_le_mul hYn hnorm' (by positivity) (Real.sqrt_nonneg _)
      _ = 2 * (X : ℝ) * Real.exp (-(L / 4)) := by
        rw [hsqrt]
        have he : Real.exp ((1 / 2 : ℝ) * L) * Real.exp ((1 / 4 : ℝ) * L) =
            Real.exp L * Real.exp (-(L / 4)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [mul_left_comm, he, Real.exp_log hXpos, mul_assoc]
      _ ≤ _ := by
        gcongr
        · exact le_max_right _ _
        · simpa only [neg_mul] using neg_le_neg hrate
  · have hYY : (X : ℝ) ≤ (Y : ℝ) ^ 2 := by exact_mod_cast (le_of_lt (lt_of_not_ge hshort))
    have hYpos : 0 < (Y : ℝ) := by
      by_contra! hn
      have hzero : (Y : ℝ) = 0 := le_antisymm hn (by positivity)
      rw [hzero] at hYY
      simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hYY
      exact hXpos.not_ge hYY
    have hlong := Real.log_le_log hXpos hYY
    rw [Real.log_pow] at hlong
    norm_num at hlong
    have hlong' : L / 2 ≤ Real.log (Y : ℝ) := by linarith
    have hroot : L ^ (1 / 2 : ℝ) ≤ L / 2 := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [mul_nonneg hL (show 0 ≤ L - 4 by linarith)]
    have hfast : L ^ (1 / 10 : ℝ) ≤ Real.log (Y : ℝ) ^ (1 / 3 : ℝ) := by
      calc
        _ ≤ L ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by norm_num)
        _ = (L ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) := Real.rpow_mul hL _ _
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hL _) (hroot.trans hlong') (by norm_num)
    have hqY : (q : ℝ) ≤ Real.exp (Real.log (Y : ℝ) ^ (1 / 3 : ℝ)) :=
      hqX.trans (Real.exp_le_exp.mpr hfast)
    have hYge : Y₀ ≤ Y := by
      by_contra! hn
      exact hshort ((Nat.pow_le_pow_left hn.le 2).trans hXY₀)
    have hlarge := hY₀ Y hYge q hq a ha hqY
    refine hlarge.trans ?_
    have hc' : c₀ * L ^ (1 / 10 : ℝ) ≤ c * Real.log (Y : ℝ) ^ (1 / 3 : ℝ) :=
      mul_le_mul hc₂ hfast (Real.rpow_nonneg hL _) hc.le
    have hexp : Real.exp (-c * Real.log (Y : ℝ) ^ (1 / 3 : ℝ)) ≤
        Real.exp (-c₀ * L ^ (1 / 10 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg hc'
    exact mul_le_mul
      (mul_le_mul (le_max_left C 2) (by exact_mod_cast hY) (Nat.cast_nonneg _) hD.le)
      hexp (Real.exp_pos _).le (by positivity)

/-- The natural-number prefix used for the prime theorem agrees with the integer interval sum. -/
theorem residueVonMangoldt_eq_interval {q : ℕ} (a : ZMod q) (Y : ℕ) :
    residueVonMangoldt a Y = ∑ n ∈ residueSlice 1 (Y : ℤ) a, vonMangoldtWeight n := by
  classical
  let e : ℕ ↪ ℤ := ⟨fun n => n, Int.ofNat_injective⟩
  let S := (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod q) = a)
  have he : S.map e = residueSlice 1 (Y : ℤ) a := by
    ext n
    simp only [S, Finset.mem_map, Finset.mem_filter, Finset.mem_Icc, residueSlice, interval,
      Finset.mem_Ico]
    constructor
    · rintro ⟨m, ⟨⟨hm₁, hmY⟩, ha⟩, rfl⟩
      change (1 ≤ (m : ℤ) ∧ (m : ℤ) < 1 + (Y : ℤ)) ∧ ((m : ℤ) : ZMod q) = a
      exact ⟨⟨by exact_mod_cast hm₁, by rw [add_comm]; exact_mod_cast Nat.lt_add_one_of_le hmY⟩,
        by rwa [Int.cast_natCast]⟩
    · rintro ⟨⟨hlo, hhi⟩, ha⟩
      have hnonneg : 0 ≤ n := by omega
      refine ⟨n.toNat, ⟨⟨by omega, by omega⟩, ?_⟩, Int.toNat_of_nonneg hnonneg⟩
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg]
      exact ha
  rw [← he, Finset.sum_map]
  rfl

/-- An interval progression mass is the difference of its two prefix masses. -/
theorem residueVonMangoldt_interval_eq_sub_prefix {q U V : ℕ} (hUV : U ≤ V) (a : ZMod q) :
    (∑ n ∈ residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a, vonMangoldtWeight n) =
      residueVonMangoldt a V - residueVonMangoldt a U := by
  classical
  rw [residueVonMangoldt_eq_interval, residueVonMangoldt_eq_interval]
  have hsubset : residueSlice 1 (U : ℤ) a ⊆ residueSlice 1 (V : ℤ) a := by
    intro n hn
    simp only [residueSlice, interval, Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hs : residueSlice 1 (V : ℤ) a \ residueSlice 1 (U : ℤ) a =
      residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a := by
    ext n
    simp only [Finset.mem_sdiff, residueSlice, interval, Finset.mem_filter, Finset.mem_Ico,
      Int.natCast_sub hUV]
    constructor
    · rintro ⟨⟨⟨hlo, hhi⟩, ha⟩, hno⟩
      exact ⟨⟨by
        by_contra! hn
        exact hno ⟨⟨hlo, by omega⟩, ha⟩, by omega⟩, ha⟩
    · rintro ⟨⟨hlo, hhi⟩, ha⟩
      exact ⟨⟨⟨by omega, by omega⟩, ha⟩, fun hn => by omega⟩
  rw [← hs]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hsubset)

/-- Uniform prime counts in reduced progressions on every subinterval of the ambient scale. -/
theorem uniform_prime_interval_of_large_modulus (h : UniformPrimePrefixEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ U V : ℕ, U ≤ V → V ≤ X → ∀ (q : ℕ), 0 < q → ∀ a : ZMod q, IsUnit a →
        (q : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ)) →
        |(∑ n ∈ residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) a, vonMangoldtWeight n) -
          ((V - U : ℕ) : ℝ) / (q.totient : ℝ)| ≤
          C * (X : ℝ) * Real.exp (-c * Real.log (X : ℝ) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, C, hc, hC, h⟩ := uniform_primePrefix_of_large_modulus h
  refine ⟨c, 2 * C, hc, by positivity, ?_⟩
  filter_upwards [h] with X hX
  intro U V hUV hVX q hq a ha hqX
  have hV := hX V hVX q hq a ha hqX
  have hU := hX U (hUV.trans hVX) q hq a ha hqX
  rw [residueVonMangoldt_interval_eq_sub_prefix hUV, Nat.cast_sub hUV, sub_div]
  have he :
      residueVonMangoldt a V - residueVonMangoldt a U - ((V : ℝ) / (q.totient : ℝ) - (U : ℝ) / (q.totient : ℝ)) =
        (residueVonMangoldt a V - (V : ℝ) / (q.totient : ℝ)) -
        (residueVonMangoldt a U - (U : ℝ) / (q.totient : ℝ)) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hV hU).trans_eq (by ring))

end PrimeUniformity
