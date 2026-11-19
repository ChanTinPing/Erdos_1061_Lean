module

public import PrimeUniformity.GowersSum
public import PrimeUniformity.IntervalMoment
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

private theorem cyclicWeight_add (X p : ℕ) (f g : ℤ → ℝ) (x : ZMod p) :
    cyclicWeight X p (fun n => f n + g n) x =
      cyclicWeight X p f x + cyclicWeight X p g x := by
  by_cases hx : 1 ≤ x.val ∧ x.val ≤ X <;> simp [cyclicWeight, hx]

/-- At each positive order, the sum estimate holds for interval moments
with the same dimension-dependent constant as for cyclic moments. -/
theorem exists_intervalCubeSum_succ_add_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ) (f g : ℤ → ℝ),
      intervalCubeSum d.succ X (fun n => f n + g n) ≤
        C * (intervalCubeSum d.succ X f + intervalCubeSum d.succ X g) := by
  obtain ⟨C, hC, hadd⟩ := exists_gowersCubeMoment_succ_add_le d
  refine ⟨C, hC, ?_⟩
  intro X f g
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes ((2 * d.succ + 2) * X + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hlarge : (2 * d.succ + 2) * X < p := by omega
  have hXp : X < p :=
    lt_of_le_of_lt (by simpa using Nat.mul_le_mul_right X (show 1 ≤ 2 * d.succ + 2 by omega)) hlarge
  have hlargeInt : (2 * (d.succ : ℤ) + 2) * X < (p : ℤ) := by exact_mod_cast hlarge
  have hmoment := hadd (cyclicWeight X p f) (cyclicWeight X p g)
  simp only [← cyclicWeight_add, gowersCubeMoment_cyclicWeight_eq_intervalCubeSum
    d.succ X p hXp hlargeInt] at hmoment
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  apply (div_le_div_iff_of_pos_right (pow_pos hpR (d.succ + 1))).mp
  simpa only [add_div, mul_div_assoc] using hmoment

/-- Every positive-order interval cube moment is nonnegative. -/
theorem intervalCubeSum_succ_nonneg (d X : ℕ) (w : ℤ → ℝ) :
    0 ≤ intervalCubeSum d.succ X w := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes ((2 * d.succ + 2) * X + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hlarge : (2 * d.succ + 2) * X < p := by omega
  have hXp : X < p :=
    lt_of_le_of_lt (by simpa using Nat.mul_le_mul_right X (show 1 ≤ 2 * d.succ + 2 by omega)) hlarge
  have hlargeInt : (2 * (d.succ : ℤ) + 2) * X < (p : ℤ) := by exact_mod_cast hlarge
  have hmoment := gowersCubeMoment_succ_nonneg d (cyclicWeight X p w)
  rw [gowersCubeMoment_cyclicWeight_eq_intervalCubeSum d.succ X p hXp hlargeInt] at hmoment
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  simpa only [zero_mul] using (le_div_iff₀ (pow_pos hpR (d.succ + 1))).mp hmoment

/-- A logarithmic bound on the normalized interval cube moment of a family of weights. -/
def IntervalMomentBound (order exponent : ℕ) (w : ℕ → ℤ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    intervalCubeSum order X (w X) ≤
      (C / (Real.log (X : ℝ)) ^ exponent) * intervalCubeSum order X (fun _ => 1)

/-- Two interval moment bounds with the same exponent give a bound for the sum,
with a constant that depends on the two original constants and the order. -/
theorem IntervalMomentBound.add {d A : ℕ} {f g : ℕ → ℤ → ℝ}
    (hf : IntervalMomentBound d.succ A f) (hg : IntervalMomentBound d.succ A g) :
    IntervalMomentBound d.succ A (fun X n => f X n + g X n) := by
  obtain ⟨C, hC, hadd⟩ := exists_intervalCubeSum_succ_add_le d
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨C * (Cf + Cg), by positivity, ?_⟩
  filter_upwards [hf, hg] with X hfX hgX
  refine (hadd X (f X) (g X)).trans ?_
  calc
    _ ≤ C * ((Cf / (Real.log (X : ℝ)) ^ A) * intervalCubeSum d.succ X (fun _ => 1) +
        (Cg / (Real.log (X : ℝ)) ^ A) * intervalCubeSum d.succ X (fun _ => 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfX hgX) hC.le
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- The two analytic comparison bounds through a common intermediate model
suffice for quantitative prime uniformity, with the same logarithmic exponent. -/
theorem gowersUniformityEstimate_of_model_comparisons (d A : ℕ) (model : ℕ → ℤ → ℝ)
    (hprime : IntervalMomentBound d.succ A (fun X n => primeWeight n - model X n))
    (hmodel : IntervalMomentBound d.succ A
      (fun X n => model X n - cramerWeight (primeUniformityCutoff X) n)) :
    GowersUniformityEstimate d.succ A := by
  apply gowersUniformityEstimate_of_interval
  have hsum : (fun X n => (primeWeight n - model X n) +
      (model X n - cramerWeight (primeUniformityCutoff X) n)) =
      (fun X n => primeWeight n - cramerWeight (primeUniformityCutoff X) n) := by
    funext X n
    ring
  have h := hprime.add hmodel
  rw [hsum] at h
  exact h

end PrimeUniformity
