module

public import Jsp000881.Reduction
import all Jsp000881.Reduction

@[expose] public section

open Filter Asymptotics
open scoped ArithmeticFunction.sigma

namespace Jsp000881

/-- The ordered-pair count in Erdős #1061, with the perimeter written as a sum in `ℝ`. -/
noncomputable def originalCount (x : ℝ) : ℝ := by
  classical
  let pairs := (Finset.Icc 1 ⌊x⌋₊).product (Finset.Icc 1 ⌊x⌋₊)
  exact ↑(pairs.filter fun (a, b) =>
    (a : ℝ) + (b : ℝ) ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

theorem originalCount_eq_S : originalCount = S := by
  funext x
  simp only [originalCount, S, solutionsBelow, Nat.cast_add]

/-- The positive answer to the asymptotic question in the original problem. -/
def OriginalQuestion : Prop :=
  ∃ c : ℝ, 0 < c ∧ originalCount ~[atTop] (fun x : ℝ => c * x)

theorem originalQuestion_iff :
    OriginalQuestion ↔ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) := by
  unfold OriginalQuestion
  rw [originalCount_eq_S]

end Jsp000881
