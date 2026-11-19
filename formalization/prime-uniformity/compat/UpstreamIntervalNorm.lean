import PrimeUniformity.IntervalNorm
import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport

namespace PrimeUniformity

open OAI.Erdos3 (cubeShift conjugationPower mixedCubeProduct supportedCubeSum finiteSupportGowersNorm)
open scoped BigOperators

private theorem conjugationPower_ofReal (k : ℕ) (x : ℝ) :
    conjugationPower k (x : ℂ) = (x : ℂ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change star (conjugationPower k (x : ℂ)) = (x : ℂ)
    rw [ih]
    simp

/-- The real-weight interval normalization equals the upstream complex-weight
normalization on the same supported integer cubes. -/
theorem intervalGowersNorm_eq_upstream (d X : ℕ) (w : ℤ → ℝ) :
    intervalGowersNorm d X w =
      finiteSupportGowersNorm d (Finset.Ico (1 : ℤ) (1 + (X : ℤ))) (fun n => (w n : ℂ)) := by
  classical
  rw [intervalGowersNorm, normalizedIntervalCubeSum_eq_supportedCubeAverage,
    finiteSupportGowersNorm, supportedCubeSum, Complex.re_sum]
  congr 1
  congr 1
  have hFintype : supportedIntervalCubeFintype d X =
      OAI.Erdos3.supportedCubeFintype d (↑(Finset.Ico (1 : ℤ) (1 + (X : ℤ))) : Set ℤ) :=
    Subsingleton.elim _ _
  rw [← hFintype]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mixedCubeProduct, conjugationPower_ofReal, ← Complex.ofReal_prod,
    Complex.ofReal_re, cubeVertex, cubeShift]

end PrimeUniformity

#print axioms PrimeUniformity.intervalGowersNorm_eq_upstream
