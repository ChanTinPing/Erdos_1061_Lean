module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The finite Fourier argument follows OAI.FejerDetection.detect in
openai/math (Apache-2.0), revision 4eaee87548250b2682affda7d05d947c05554bae.
Here the averaging set is arbitrary and the phase is the ordinary real
additive character.
-/

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

/-- The ordinary additive phase on the real line. -/
noncomputable def recurrencePhase (x : ℝ) : ℂ :=
  Complex.exp ((Complex.ofReal (2 * Real.pi * x)) * Complex.I)

/-- Subtracting arguments multiplies the phase by a conjugate. -/
theorem recurrencePhase_sub (x y : ℝ) :
    recurrencePhase (x - y) = recurrencePhase x * conj (recurrencePhase y) := by
  rw [recurrencePhase, recurrencePhase, recurrencePhase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Integer arguments have trivial phase. -/
theorem recurrencePhase_int (z : ℤ) : recurrencePhase (z : ℝ) = 1 := by
  rw [recurrencePhase, ← Complex.exp_int_mul_two_pi_mul_I z]
  congr 1
  push_cast
  ring

private theorem recurrencePhase_close {x ε : ℝ} {z : ℤ} (hx : |x - z| ≤ ε) :
    ‖recurrencePhase x - 1‖ ≤ 2 * Real.pi * ε := by
  have he : recurrencePhase (x - z) = recurrencePhase x := by
    rw [recurrencePhase_sub, recurrencePhase_int, map_one, mul_one]
  rw [← he, recurrencePhase, mul_comm]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

private theorem norm_average_sq {ι : Type*} (U : Finset ι) (f : ι → ℂ) :
    ‖𝔼 i ∈ U, f i‖ ^ 2 = 𝔼 i ∈ U, 𝔼 j ∈ U, (f i * conj (f j)).re := by
  have hc : conj (𝔼 i ∈ U, f i) = 𝔼 i ∈ U, conj (f i) :=
    map_expect (Complex.conjAe.toLinearMap.restrictScalars ℚ≥0) f U
  rw [← Complex.ofReal_re (r := ‖𝔼 i ∈ U, f i‖ ^ 2)]
  rw [Complex.ofReal_pow, ← Complex.mul_conj', hc, Finset.expect_mul_expect]
  simp only [Complex.re_expect]

/-- A dense set of near-integer phase values forces correlation at a nonzero
frequency of magnitude less than `R`. All averages are over finite sets. -/
theorem large_phase_average_of_near_integers {ι : Type*} (T S : Finset ι)
    (hT : T.Nonempty) (hST : S ⊆ T) (R : ℕ) (hR : 0 < R)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hRρ : 16 ≤ ρ * R) (hsmall : 2 * Real.pi * R * ε ≤ 1 / 2)
    (hdense : ρ * (T.card : ℝ) ≤ S.card)
    (f : ι → ℝ) (hnear : ∀ n ∈ S, ∃ z : ℤ, |f n - z| ≤ ε) :
    ∃ a ∈ Finset.range R, ∃ b ∈ Finset.range R, a ≠ b ∧
      ρ / 16 ≤ ‖𝔼 n ∈ T, recurrencePhase (((a : ℝ) - b) * f n)‖ := by
  classical
  let U := Finset.range R
  have hU : U.Nonempty := Finset.nonempty_range_iff.mpr hR.ne'
  let E (n : ι) := ‖𝔼 a ∈ U, recurrencePhase ((a : ℝ) * f n)‖ ^ 2
  have hE (n : ι) (hn : n ∈ S) : 1 / 4 ≤ E n := by
    obtain ⟨z, hz⟩ := hnear n hn
    let A (a : ℕ) := recurrencePhase ((a : ℝ) * f n)
    have hpoint (a : ℕ) (ha : a ∈ U) : ‖A a - 1‖ ≤ 1 / 2 := by
      have hnear' : |(a : ℝ) * f n - (((a : ℤ) * z : ℤ) : ℝ)| ≤ (a : ℝ) * ε := by
        simp only [Int.cast_mul, Int.cast_natCast, ← mul_sub, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg a : 0 ≤ (a : ℝ))]
        exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg a)
      have ha' : (a : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp ha).le
      refine (recurrencePhase_close hnear').trans ?_
      rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha' (by positivity : 0 ≤ 2 * Real.pi)) hε).trans hsmall
    have havg : ‖(𝔼 a ∈ U, A a) - 1‖ ≤ 1 / 2 := by
      rw [← U.expect_const hU (1 : ℂ), ← Finset.expect_sub_distrib]
      exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hU hpoint)
    have hnorm := norm_le_norm_add_norm_sub (𝔼 a ∈ U, A a) (1 : ℂ)
    rw [norm_one] at hnorm
    change (1 : ℝ) / 4 ≤ ‖𝔼 a ∈ U, A a‖ ^ 2
    nlinarith [norm_nonneg (𝔼 a ∈ U, A a)]
  have hlower : ρ / 4 ≤ 𝔼 n ∈ T, E n := by
    rw [Finset.expect_eq_sum_div_card]
    apply (le_div_iff₀ (Nat.cast_pos.mpr hT.card_pos)).mpr
    have hgood := Finset.sum_le_sum hE
    simp only [Finset.sum_const, nsmul_eq_mul] at hgood
    have hnonneg := Finset.sum_le_sum_of_subset_of_nonneg hST
      (fun n _ _ => sq_nonneg ‖𝔼 a ∈ U, recurrencePhase ((a : ℝ) * f n)‖)
    nlinarith
  have hexpand : (𝔼 n ∈ T, E n) = 𝔼 a ∈ U, 𝔼 b ∈ U,
      (𝔼 n ∈ T, recurrencePhase (((a : ℝ) - b) * f n)).re := by
    unfold E
    simp_rw [norm_average_sq, Complex.re_expect]
    rw [Finset.expect_comm T U]
    refine Finset.expect_congr rfl (fun a _ => ?_)
    rw [Finset.expect_comm T U]
    refine Finset.expect_congr rfl (fun b _ => Finset.expect_congr rfl (fun n _ => ?_))
    rw [sub_mul, recurrencePhase_sub]
  by_contra! hno
  have hmode (a : ℕ) (ha : a ∈ U) (b : ℕ) (hb : b ∈ U) :
      (𝔼 n ∈ T, recurrencePhase (((a : ℝ) - b) * f n)).re ≤
        (if a = b then 1 else 0) + ρ / 16 := by
    by_cases hab : a = b
    · subst b
      simpa [recurrencePhase, Finset.expect_const hT] using (div_nonneg hρ.le (by norm_num : (0 : ℝ) ≤ 16))
    · exact (Complex.re_le_norm _).trans (by simpa [hab] using (hno a ha b hb hab).le)
  have hdiag (a : ℕ) (ha : a ∈ U) :
      (𝔼 b ∈ U, ((if a = b then 1 else 0) + ρ / 16)) = 1 / (R : ℝ) + ρ / 16 := by
    rw [Finset.expect_add_distrib, Finset.expect_const hU, Finset.expect_eq_sum_div_card]
    simp [U, Finset.sum_ite_eq, ha]
  have hupper := Finset.expect_le_expect (fun a ha =>
    Finset.expect_le_expect (fun b hb => hmode a ha b hb))
  rw [Finset.expect_congr rfl hdiag, Finset.expect_const hU, ← hexpand] at hupper
  have hrecip : 1 / (R : ℝ) ≤ ρ / 16 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hR)).mpr
    nlinarith
  linarith

/-- A positive frequency can always be chosen because the phase is real-valued
before exponentiation and the two signs give conjugate averages. -/
theorem large_positive_phase_average_of_near_integers {ι : Type*} (T S : Finset ι)
    (hT : T.Nonempty) (hST : S ⊆ T) (R : ℕ) (hR : 0 < R)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hRρ : 16 ≤ ρ * R) (hsmall : 2 * Real.pi * R * ε ≤ 1 / 2)
    (hdense : ρ * (T.card : ℝ) ≤ S.card)
    (f : ι → ℝ) (hnear : ∀ n ∈ S, ∃ z : ℤ, |f n - z| ≤ ε) :
    ∃ m : ℕ, 0 < m ∧ m < R ∧ ρ / 16 ≤ ‖𝔼 n ∈ T, recurrencePhase ((m : ℝ) * f n)‖ := by
  obtain ⟨a, ha, b, hb, hab, hc⟩ :=
    large_phase_average_of_near_integers T S hT hST R hR ρ ε hρ hε hRρ hsmall hdense f hnear
  have haR := Finset.mem_range.mp ha
  have hbR := Finset.mem_range.mp hb
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨b - a, by omega, by omega, ?_⟩
    have he (n : ι) : recurrencePhase (((a : ℝ) - b) * f n) =
        conj (recurrencePhase (((b - a : ℕ) : ℝ) * f n)) := by
      rw [Nat.cast_sub h.le]
      have harg : ((a : ℝ) - b) * f n = 0 - ((b : ℝ) - a) * f n := by ring
      rw [harg, recurrencePhase_sub]
      simp [recurrencePhase]
    have hc' : conj (𝔼 n ∈ T, recurrencePhase (((b - a : ℕ) : ℝ) * f n)) =
        𝔼 n ∈ T, conj (recurrencePhase (((b - a : ℕ) : ℝ) * f n)) :=
      map_expect (Complex.conjAe.toLinearMap.restrictScalars ℚ≥0) _ T
    simpa only [he, ← hc', Complex.norm_conj] using hc
  · refine ⟨a - b, by omega, by omega, ?_⟩
    simpa only [Nat.cast_sub h.le] using hc

end PrimeUniformity
