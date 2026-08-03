module

public import Topology_Munkres_2000.Book.Exercise_51_3.Contractible

public section

/- Exercise 51.3 check surface. -/
#check contractible_iff_id_nullhomotopic
#check unitInterval.instContractibleSpace
#synth ContractibleSpace ℝ
#check ContinuousMap.Homotopic.Quotient.nonemptyUniqueOfContractibleCodomain
#check ContinuousMap.Homotopic.Quotient.nonemptyUniqueOfContractibleDomain

/-- The defining characterization in Exercise 51.3: a space `X` is contractible exactly
when its identity map is nullhomotopic. -/
theorem contractibleSpace_iff_identity_nullhomotopic (X : Type*) [TopologicalSpace X] :
    ContractibleSpace X ↔ (ContinuousMap.id X).Nullhomotopic := by
  -- Use mathlib's characterization by nullhomotopy of the identity.
  exact contractible_iff_id_nullhomotopic X

/-- Part (a) of Exercise 51.3: The unit interval and the real line are contractible. -/
theorem unitIntervalAndReal_contractible :
    ContractibleSpace unitInterval ∧ ContractibleSpace ℝ := by
  -- Both standard spaces carry the canonical contractible-space instances.
  exact And.intro inferInstance inferInstance

/-- Part (b) of Exercise 51.3: Every contractible space is path connected. -/
theorem pathConnectedSpace_of_contractibleSpace (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] : PathConnectedSpace X := by
  -- Contractibility supplies the canonical path-connected-space instance.
  exact inferInstance

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Part (c) of Exercise 51.3: If `Y` is contractible, then `⟦X, Y⟧ₕ` has exactly one element. -/
theorem homotopyClassesUnique_of_contractibleCodomain [ContractibleSpace Y] :
    Nonempty (Unique ⟦X, Y⟧ₕ) := by
  -- All maps contract through the codomain to one homotopy class.
  exact ContinuousMap.Homotopic.Quotient.nonemptyUniqueOfContractibleCodomain

/-- Part (d) of Exercise 51.3: If `X` is contractible and `Y` is path connected, then `⟦X, Y⟧ₕ` has
exactly one element. -/
theorem homotopyClassesUnique_of_contractibleDomain [ContractibleSpace X]
    [PathConnectedSpace Y] : Nonempty (Unique ⟦X, Y⟧ₕ) := by
  -- Contract the domain and join the resulting constant maps in the codomain.
  exact ContinuousMap.Homotopic.Quotient.nonemptyUniqueOfContractibleDomain
