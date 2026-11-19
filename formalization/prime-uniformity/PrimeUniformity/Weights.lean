module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The weight `log n` on positive prime integers, with zero elsewhere. -/
noncomputable def primeWeight (n : ℤ) : ℝ :=
  if n.toNat.Prime then Real.log (n : ℝ) else 0

/-- The primes at most `Q`. -/
noncomputable def cramerPrimeSet (Q : ℕ) : Finset ℕ :=
  (Finset.range (Q + 1)).filter Nat.Prime

/-- The normalizing product for Cramér's model at cutoff `Q`. -/
noncomputable def cramerNormalization (Q : ℕ) : ℝ :=
  ∏ p ∈ cramerPrimeSet Q, (1 - 1 / (p : ℝ))⁻¹

/-- Finite Cramér weight at the prime cutoff `Q`. -/
noncomputable def cramerWeight (Q : ℕ) (n : ℤ) : ℝ := by
  classical
  exact if ∀ p ∈ cramerPrimeSet Q, ¬ (p : ℤ) ∣ n then cramerNormalization Q else 0

/-- Cramér's cutoff used by the quantitative prime uniformity estimate. -/
noncomputable def primeUniformityCutoff (X : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (X : ℝ) ^ (1 / 10 : ℝ))⌋₊

/-- Place an integer weight on representatives 1 through X, with zero elsewhere. -/
noncomputable def cyclicWeight (X p : ℕ) (w : ℤ → ℝ) (x : ZMod p) : ℂ :=
  if 1 ≤ x.val ∧ x.val ≤ X then (w (x.val : ℤ) : ℂ) else 0

theorem cyclicWeight_intCast {X p : ℕ} (hXp : X < p) (w : ℤ → ℝ) {n : ℤ}
    (hn : 1 ≤ n) (hnX : n ≤ (X : ℤ)) :
    cyclicWeight X p w (n : ZMod p) = (w n : ℂ) := by
  letI : NeZero p := ⟨(Nat.zero_lt_of_lt hXp).ne'⟩
  have hX : (X : ℤ) < (p : ℤ) := by exact_mod_cast hXp
  have hv : ((n : ZMod p).val : ℤ) = n := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (hnX.trans_lt hX)]
  have hlo : 1 ≤ (n : ZMod p).val := by
    exact_mod_cast (show (1 : ℤ) ≤ ((n : ZMod p).val : ℤ) by rw [hv]; exact hn)
  have hhi : (n : ZMod p).val ≤ X := by
    exact_mod_cast (show ((n : ZMod p).val : ℤ) ≤ (X : ℤ) by rw [hv]; exact hnX)
  have hs : 1 ≤ (n : ZMod p).val ∧ (n : ZMod p).val ≤ X := ⟨hlo, hhi⟩
  simp only [cyclicWeight, if_pos hs, hv]

theorem norm_cyclicWeight_le {X p : ℕ} {w : ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |w n| ≤ B) (x : ZMod p) :
    ‖cyclicWeight X p w x‖ ≤ B := by
  unfold cyclicWeight
  split
  · rename_i hx
    simpa using hw (x.val : ℤ) (by exact_mod_cast hx.1) (by exact_mod_cast hx.2)
  · simpa only [norm_zero] using hB

/-- Zero-extended difference of the true-prime and Cramér weights. -/
noncomputable def primeCramerDifference (X p : ℕ) : ZMod p → ℂ :=
  cyclicWeight X p (fun n => primeWeight n - cramerWeight (primeUniformityCutoff X) n)

theorem primeCramerDifference_intCast {X p : ℕ} (hXp : X < p) {n : ℤ}
    (hn : 1 ≤ n) (hnX : n ≤ (X : ℤ)) :
    primeCramerDifference X p (n : ZMod p) =
      ((primeWeight n - cramerWeight (primeUniformityCutoff X) n : ℝ) : ℂ) :=
  cyclicWeight_intCast hXp _ hn hnX

end PrimeUniformity
