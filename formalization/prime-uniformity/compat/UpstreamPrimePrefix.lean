import PrimeUniformity.PrimeProgressions
import OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz

namespace PrimeUniformity

open Filter
open OAI.Erdos970.Erdos970Dependency.SiegelWalfisz (cubeHeight residuePsi residuePsi_exponential)

theorem upstream_uniformPrimePrefix : UniformPrimePrefixEstimate := by
  refine UniformPrimePrefixEstimate.of_real_range ?_
  obtain ⟨c, C, hc, _, hC, h⟩ := residuePsi_exponential
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [h] with Y hY
  intro q _ a ha hq
  simpa only [cubeHeight, residuePsi, ArithmeticFunction.vonMangoldt.residueClass,
    Set.indicator_apply, Set.mem_ofPred_eq] using hY q a ha hq

end PrimeUniformity

#print axioms PrimeUniformity.upstream_uniformPrimePrefix

#print axioms OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.residuePsi_exponential
