module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Homotopy.Equiv

public section

universe u v

namespace ContinuousMap.HomotopyEquiv

/-- A homotopy equivalence induces a bijective homomorphism on fundamental groups
at the image of each basepoint. -/
theorem fundamentalGroupMap_bijective {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (x₀ : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x₀) := by
  -- The induced equivalence of fundamental groupoids is fully faithful on loops.
  exact (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₀)

end ContinuousMap.HomotopyEquiv

end
