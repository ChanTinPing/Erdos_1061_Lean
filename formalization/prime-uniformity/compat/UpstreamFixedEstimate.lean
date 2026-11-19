import UpstreamNativePrimeTests
import UpstreamPrimePrefix

namespace PrimeUniformity

/-- With both upstream inputs instantiated, the only remaining hypothesis
for JSP is step descent for the concrete native test family. -/
theorem gowersUniformityEstimate_of_native_step_descent
    (hdescent : PrimeCramerStepDescent 4 nativePrimeTests) :
    GowersUniformityEstimate 5 1280 :=
  gowersUniformityEstimate_of_native_prime_descent upstream_uniformPrimePrefix hdescent

end PrimeUniformity

#print axioms PrimeUniformity.gowersUniformityEstimate_of_native_step_descent
