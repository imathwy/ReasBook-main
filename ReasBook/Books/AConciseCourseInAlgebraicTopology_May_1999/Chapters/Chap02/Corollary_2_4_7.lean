import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] [ContractibleSpace X]

/-- A contractible space has trivial fundamental group at every basepoint. -/
instance subsingletonFundamentalGroupOfContractible (x : X) :
    Subsingleton (FundamentalGroup X x) := by
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- Corollary 2.4.7: a contractible space has trivial fundamental group at every basepoint. -/
theorem fundamentalGroup_subsingleton_of_contractible (x : X) :
    Subsingleton (FundamentalGroup X x) :=
  inferInstance
