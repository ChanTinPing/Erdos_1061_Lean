module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

namespace Jsp000881

/-- A nontrivial unit-modulus additive character of the prime residue field. -/
theorem exists_unit_additive_character (p : ℕ) [Fact p.Prime] :
    ∃ χ : ZMod p → ℂ, χ 0 = 1 ∧ (∀ t, ‖χ t‖ = 1) ∧
      (∀ u v, χ (u + v) = χ u * χ v) ∧ (∃ t, χ t ≠ 1) := by
  have hp : p.Prime := Fact.out
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let r : ℝ := 2 * Real.pi / p
  let ζ := Complex.exp ((r : ℂ) * Complex.I)
  have hζp : ζ ^ p = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    have he : (p : ℂ) * ((r : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      dsimp [r]
      push_cast
      field_simp [hpC] <;> ring
    rw [he, Complex.exp_two_pi_mul_I]
  have hζ : ζ ≠ 1 := by
    intro h
    have he : ζ = Complex.exp (2 * Real.pi * Complex.I * (1 : ℕ) / (p : ℂ)) := by
      dsimp [ζ, r]
      push_cast
      congr 1
      ring
    exact hp.ne_one (Nat.dvd_one.mp
      ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hp.ne_zero).mp (he.symm.trans h)))
  have hnorm : ‖ζ‖ = 1 := by
    dsimp only [ζ]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  refine ⟨fun t => ζ ^ t.val, by simp, ?_, ?_, ?_⟩
  · intro t
    simp [norm_pow, hnorm]
  · intro u v
    change ζ ^ (u + v).val = ζ ^ u.val * ζ ^ v.val
    rw [ZMod.val_add, ← pow_eq_pow_mod (u.val + v.val) hζp, pow_add]
  · refine ⟨1, ?_⟩
    change ζ ^ (1 : ZMod p).val ≠ 1
    rwa [ZMod.val_one'' hp.ne_one, pow_one]

end Jsp000881
