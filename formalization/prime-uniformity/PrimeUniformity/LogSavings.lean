module

public import Mathlib.Algebra.Polynomial.Degree.Defs

public import PrimeUniformity.IntervalBounds
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open Filter

private theorem eventually_one_le_log : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
  ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)

private theorem intervalCubeSum_unit_nonneg (d X : ℕ) :
    0 ≤ intervalCubeSum d X (fun _ => 1) := by
  rw [intervalCubeSum_one_eq_card]
  positivity

/-- Any positive power of the ambient scale absorbs a stretched exponential
with a fixed coefficient and logarithmic exponent less than one. -/
theorem eventually_exp_mul_log_rpow_le_rpow {c K a : ℝ}
    (hc : c < 1) (ha : 0 < a) :
    ∀ᶠ X : ℕ in atTop, Real.exp (K * Real.log (X : ℝ) ^ c) ≤ (X : ℝ) ^ a := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (1 - c)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hc)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (K / a), eventually_one_le_log,
    eventually_ge_atTop (1 : ℕ)] with X hpow hlog hX
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hX)
  let L := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hsplit : L ^ (1 - c) * L ^ c = L := by
    rw [← Real.rpow_add hL, sub_add_cancel, Real.rpow_one]
  have hcompare := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hpow)
    (Real.rpow_nonneg hL.le c)
  rw [mul_right_comm, hsplit] at hcompare
  rw [Real.rpow_def_of_pos hXpos]
  exact Real.exp_le_exp.mpr hcompare

private theorem natPolynomial_eval_le_scaled_pow (P : Polynomial ℕ) (n : ℕ) {y : ℝ}
    (hy : 1 ≤ y) (hn : (n : ℝ) ≤ y) :
    ((P.eval n : ℕ) : ℝ) ≤ ((P.eval 1 : ℕ) : ℝ) * y ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range n, Polynomial.eval_eq_sum_range (1 : ℕ)]
  push_cast
  simp only [one_pow, mul_one, Finset.sum_mul]
  refine Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _).trans
    (pow_le_pow_right₀ hy (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

/-- An exponential bound on the input gives a linear bound on the
logarithm of a natural polynomial's value. -/
theorem natPolynomial_eval_le_exp (P : Polynomial ℕ) (n : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp p) :
    (↑(P.eval n) : ℝ) ≤ Real.exp (↑(P.eval 1) + (P.natDegree : ℝ) * p) := by
  have hC : (↑(P.eval 1) : ℝ) ≤ Real.exp (↑(P.eval 1)) := by
    linarith [Real.add_one_le_exp (↑(P.eval 1))]
  calc
    _ ≤ (↑(P.eval 1) : ℝ) * (Real.exp p) ^ P.natDegree :=
      natPolynomial_eval_le_scaled_pow P n (Real.one_le_exp_iff.mpr hp) hn
    _ ≤ Real.exp (↑(P.eval 1)) * (Real.exp p) ^ P.natDegree :=
      mul_le_mul_of_nonneg_right hC (pow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- Polynomial losses in a parameter that grows at a stretched exponential
rate are eventually below any fixed positive power of the ambient scale. -/
theorem eventually_natPolynomial_eval_le_rpow (P : Polynomial ℕ) (n : ℕ → ℕ)
    {c K a : ℝ} (hc : 0 ≤ c) (hc₁ : c < 1) (hK : 0 ≤ K) (ha : 0 < a)
    (hn : ∀ᶠ X : ℕ in atTop, (n X : ℝ) ≤ Real.exp (K * Real.log (X : ℝ) ^ c)) :
    ∀ᶠ X : ℕ in atTop, ((P.eval (n X) : ℕ) : ℝ) ≤ (X : ℝ) ^ a := by
  let C : ℝ := (P.eval (1 : ℕ) : ℕ)
  let D : ℝ := C + (P.natDegree : ℝ) * K
  have hC : 0 ≤ C := Nat.cast_nonneg _
  filter_upwards [hn, eventually_one_le_log, eventually_exp_mul_log_rpow_le_rpow (K := D) hc₁ ha]
    with X hn hX hbudget
  let S := Real.log (X : ℝ) ^ c
  have hS : 1 ≤ S := Real.one_le_rpow hX hc
  have hK' : 0 ≤ K * S := mul_nonneg hK (zero_le_one.trans hS)
  calc
    _ ≤ Real.exp (C + (P.natDegree : ℝ) * (K * S)) := natPolynomial_eval_le_exp P _ hK' hn
    _ ≤ Real.exp (D * S) := Real.exp_le_exp.mpr (by
      dsimp only [D]
      nlinarith only [le_mul_of_one_le_right hC hS])
    _ ≤ _ := hbudget

/-- A stretched exponential in the logarithm exceeds every fixed power of the logarithm. -/
theorem eventually_log_pow_le_exp_log_rpow (A : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) ^ A ≤ Real.exp (Real.log (X : ℝ) ^ c) := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have he := ht.eventually ((isLittleO_rpow_exp_atTop ((A : ℝ) / c)).bound one_pos)
  filter_upwards [he, eventually_one_le_log] with X hex hlog
  let L := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hpow : (L ^ c) ^ ((A : ℝ) / c) = L ^ A := by
    rw [← Real.rpow_mul hL.le, show c * ((A : ℝ) / c) = A by field_simp [hc.ne'],
      Real.rpow_natCast]
  change ‖(L ^ c) ^ ((A : ℝ) / c)‖ ≤ 1 * ‖Real.exp (L ^ c)‖ at hex
  simpa only [hpow, one_mul, Real.norm_of_nonneg (pow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.exp_pos _).le] using hex

/-- Stretched exponential decay in the logarithm implies every fixed logarithmic saving. -/
theorem IntervalMomentBound.of_stretched_exponential {d : ℕ} {w : ℕ → ℤ → ℝ}
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (h : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d X (w X) ≤
        (C * Real.exp (-(Real.log (X : ℝ) ^ c))) * intervalCubeSum d X (fun _ => 1))
    (A : ℕ) : IntervalMomentBound d A w := by
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_log_pow_le_exp_log_rpow A hc, eventually_one_le_log] with X hX hex hlog
  let L := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hrate : C * Real.exp (-(L ^ c)) ≤ C / L ^ A := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hC.le (pow_pos hL _) hex
  exact hX.trans (mul_le_mul_of_nonneg_right hrate (intervalCubeSum_unit_nonneg d X))

/-- Lower bounds on the exceptional modulus when one exists at the given scale. -/
def ExceptionalModulusGrowth (q : ℕ → Option ℕ) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop,
    ∀ m : ℕ, q X = some m → D * Real.log (X : ℝ) ^ B ≤ (m : ℝ)

/-- The standard comparison of upper and lower bounds on the distance of the
exceptional zero from one forces super-polylogarithmic modulus growth. -/
theorem exceptionalModulusGrowth_of_gap_bounds (q : ℕ → Option ℕ) (gap : ℕ → ℝ)
    {E s : ℝ} (hE : 0 < E) (hs : 0 < s)
    (hupper : ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, q X = some m →
      gap X ≤ E / Real.log (X : ℝ) ^ s)
    (hlower : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop,
      ∀ m : ℕ, q X = some m → 0 < m ∧ D / (m : ℝ) ^ ε ≤ gap X) :
    ExceptionalModulusGrowth q := by
  intro B hB
  let r := (B + 1) / s
  have hr : 0 < r := div_pos (by linarith) hs
  obtain ⟨D, hD, hlower⟩ := hlower r⁻¹ (inv_pos.mpr hr)
  refine ⟨(D / E) ^ r, Real.rpow_pos_of_pos (div_pos hD hE) _, ?_⟩
  filter_upwards [hupper, hlower, eventually_one_le_log] with X hu hl hL
  intro m hm
  let L := Real.log (X : ℝ)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hmr : 0 < (m : ℝ) := by exact_mod_cast (hl m hm).1
  have hgap := (hl m hm).2.trans (hu m hm)
  have hcmp : (D / E) * L ^ s ≤ (m : ℝ) ^ r⁻¹ := by
    have hineq := (div_le_div_iff₀ (Real.rpow_pos_of_pos hmr _)
      (Real.rpow_pos_of_pos hLpos _)).mp hgap
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hE).mpr (by simpa only [mul_comm] using hineq)
  have hgrow := Real.rpow_le_rpow (by positivity : 0 ≤ (D / E) * L ^ s) hcmp hr.le
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hLpos.le _),
    ← Real.rpow_mul hLpos.le, ← Real.rpow_mul hmr.le,
    inv_mul_cancel₀ hr.ne', Real.rpow_one] at hgrow
  have hsr : s * r = B + 1 := by dsimp [r]; field_simp [hs.ne']
  rw [hsr] at hgrow
  refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
    (Real.rpow_nonneg (div_nonneg hD.le hE.le) _)).trans hgrow

/-- A power-saving bound in the exceptional modulus, together with modulus growth,
gives any fixed logarithmic saving. The correction vanishes in the branch with no zero. -/
theorem IntervalMomentBound.of_modulus_power_saving {d : ℕ} {w : ℕ → ℤ → ℝ}
    {q : ℕ → Option ℕ} {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hq : ExceptionalModulusGrowth q)
    (h : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d X (w X) ≤
        (match q X with
        | none => 0
        | some m => C / (m : ℝ) ^ c) * intervalCubeSum d X (fun _ => 1))
    (A : ℕ) : IntervalMomentBound d A w := by
  obtain ⟨D, hD, hq⟩ := hq ((A : ℝ) / c) (div_nonneg (Nat.cast_nonneg _) hc.le)
  refine ⟨C / D ^ c, div_pos hC (Real.rpow_pos_of_pos hD _), ?_⟩
  filter_upwards [h, hq, eventually_one_le_log] with X hX hq hlog
  let L := Real.log (X : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  apply hX.trans
  apply mul_le_mul_of_nonneg_right _ (intervalCubeSum_unit_nonneg d X)
  cases he : q X with
  | none => positivity
  | some m =>
    have hm := hq m he
    have hmpos : 0 < (m : ℝ) := (mul_pos hD (Real.rpow_pos_of_pos hL _)).trans_le hm
    have hpow := Real.rpow_le_rpow
      (by positivity : 0 ≤ D * L ^ ((A : ℝ) / c)) hm hc.le
    rw [Real.mul_rpow hD.le (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hL.le,
      div_mul_cancel₀ _ hc.ne', Real.rpow_natCast] at hpow
    rw [div_div]
    exact div_le_div_of_nonneg_left hC.le (mul_pos (Real.rpow_pos_of_pos hD _) (pow_pos hL _)) hpow

end PrimeUniformity
