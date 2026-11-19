module

public import Mathlib.NumberTheory.Bertrand

public section

namespace Jsp000881

/-- Keep all integer cube relations inside a prime cyclic group whose
size is comparable to the support radius. -/
theorem exists_ambient_prime (R : ℕ) (hR : 0 < R) :
    ∃ p : ℕ, p.Prime ∧ 32 * R < p ∧ p ≤ 64 * R := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (32 * R) (by positivity)
  refine ⟨p, hp, hlo, ?_⟩
  calc
    p ≤ 2 * (32 * R) := hhi
    _ = (2 * 32) * R := (Nat.mul_assoc 2 32 R).symm
    _ = 64 * R := rfl

end Jsp000881
