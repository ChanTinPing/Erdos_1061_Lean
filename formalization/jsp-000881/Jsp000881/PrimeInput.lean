module

public import Jsp000881.ModelTransfer
import all Jsp000881.ModelTransfer
public import Jsp000881.GowersIteration
import all Jsp000881.GowersIteration
public import PrimeUniformity.Estimate

public section

namespace Jsp000881

export PrimeUniformity (primeUniformityCutoff cyclicWeight cyclicWeight_intCast
  norm_cyclicWeight_le primeCramerDifference primeCramerDifference_intCast)

/-- The fixed fifth-moment prime estimate used by the six-form reduction. -/
abbrev QuantitativePrimeGowersUniformity : Prop :=
  PrimeUniformity.GowersUniformityEstimate 5 1280

end Jsp000881
