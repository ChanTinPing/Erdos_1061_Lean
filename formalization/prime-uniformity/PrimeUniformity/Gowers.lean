module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.BigOperators

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

/-- The normalized real average over a finite type. -/
noncomputable def meanR {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card A : ℝ)

/-- The normalized complex average over a finite type. -/
noncomputable def meanC {A : Type*} [Fintype A] (f : A → ℂ) : ℂ :=
  (∑ x, f x) / (Fintype.card A : ℂ)

/-- The multiplicative difference with increment `h`. -/
def difference {A : Type*} [Add A] (h : A) (f : A → ℂ) (x : A) : ℂ :=
  f x * conj (f (x + h))

/-- For positive order `r`, the `2^r`-th power of the Gowers norm over a finite field. -/
noncomputable def gowersCubeMoment {K : Type*} [Add K] [Fintype K] : ℕ → (K → ℂ) → ℝ
  | 0, f => (meanC f).re
  | n + 1, f => meanR fun h => gowersCubeMoment n (difference h f)

end PrimeUniformity
