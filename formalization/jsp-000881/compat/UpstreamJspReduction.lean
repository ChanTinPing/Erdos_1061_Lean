import Jsp000881.OriginalProblem
import Jsp000881.PrimeReduction
import UpstreamFixedEstimate
import UpstreamVerticalDescent
import UpstreamPrimeRankIteration
import UpstreamPrimePreparedRankStep
import UpstreamTypeIUniformFromVaughan
import UpstreamTypeIIVaughanBranch

namespace Jsp000881

open Asymptotics Filter

/-- The original Erdős #1061 statement, conditional on step descent for
the concrete native prime tests. -/
theorem not_linear_asymptotic_of_native_step_descent
    (hdescent : PrimeUniformity.PrimeCramerStepDescent 4 PrimeUniformity.nativePrimeTests) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_prime_uniformity
    (PrimeUniformity.gowersUniformityEstimate_of_native_step_descent hdescent)

/-- The remaining hypothesis concerns only nonzero vertical frequencies. -/
theorem not_linear_asymptotic_of_native_vertical_step_descent
    (hdescent : PrimeUniformity.NativePrimeVerticalStepDescent 4) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_native_step_descent
    (PrimeUniformity.native_prime_step_descent_of_vertical hdescent)

/-- A single uniform decrease of rank supplies the bounded step descent
used by the original counting statement. -/
theorem not_linear_asymptotic_of_native_rank_step_descent
    (hdescent : PrimeUniformity.NativePrimeRankStepDescent 4) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_native_step_descent
    (PrimeUniformity.native_prime_step_descent_of_rank_step hdescent)

/-- It suffices to handle the two Vaughan branches for a prepared native
test with nonzero top-rank frequency. -/
theorem not_linear_asymptotic_of_native_prepared_rank_step_descent
    (hdescent : PrimeUniformity.NativePrimePreparedRankStepDescent 4) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_native_rank_step_descent
    (PrimeUniformity.native_prime_rank_step_descent_of_prepared hdescent)

/-- Erdős problem #1061 has a negative answer. -/
theorem not_linear_asymptotic : ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) :=
  not_linear_asymptotic_of_native_step_descent
    (PrimeUniformity.native_prime_step_descent_of_prepared_branches
      (fun k _ => PrimeUniformity.native_prime_prepared_typeI_branch k)
      (fun k _ => PrimeUniformity.native_prime_prepared_typeII_branch k))

/-- The negative answer expressed using the original ordered-pair count. -/
theorem erdos_1061 : ¬ OriginalQuestion :=
  fun h => not_linear_asymptotic (originalQuestion_iff.mp h)

end Jsp000881

#print axioms Jsp000881.not_linear_asymptotic_of_native_step_descent
#print axioms Jsp000881.not_linear_asymptotic_of_native_vertical_step_descent
#print axioms Jsp000881.not_linear_asymptotic_of_native_rank_step_descent
#print axioms Jsp000881.not_linear_asymptotic_of_native_prepared_rank_step_descent
#print axioms Jsp000881.not_linear_asymptotic
#print axioms Jsp000881.erdos_1061
