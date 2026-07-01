import Mathlib

universe u

open scoped Manifold

-- Semantic search note: the requested `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked directly against mathlib's `MeromorphicAt`, `OnePoint`, and
-- manifold chart API, together with the local complex-manifold precedent in this section.

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition VI.4-extra-10: a meromorphic function on a complex manifold is a continuous map to
the Riemann sphere `OnePoint ℂ` whose expression in the preferred complex chart at each point is,
away from that point, represented by a complex meromorphic function of the local coordinate. -/
structure MeromorphicFunction (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] extends ContinuousMap X (OnePoint ℂ) where
  local_meromorphic :
    ∀ x : X,
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ (extChartAt 𝓘(ℂ) x).source ∧
        ∃ g : ℂ → ℂ,
          MeromorphicAt g ((extChartAt 𝓘(ℂ) x) x) ∧
            Set.EqOn toContinuousMap
              (fun y ↦ (g ((extChartAt 𝓘(ℂ) x) y) : OnePoint ℂ))
              (U \ {x})

/-- A meromorphic function can be used as its underlying map to the Riemann sphere. -/
noncomputable instance {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] :
    CoeFun (MeromorphicFunction X) (fun _ ↦ X → OnePoint ℂ) where
  coe f := f.toContinuousMap

namespace MeromorphicFunction

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- A meromorphic function admits, in the preferred chart at each point, a punctured-neighborhood
description by a complex meromorphic function of the local coordinate. -/
theorem exists_local_representative (f : MeromorphicFunction X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ (extChartAt 𝓘(ℂ) x).source ∧
      ∃ g : ℂ → ℂ,
        MeromorphicAt g ((extChartAt 𝓘(ℂ) x) x) ∧
          Set.EqOn f
            (fun y ↦ (g ((extChartAt 𝓘(ℂ) x) y) : OnePoint ℂ))
            (U \ {x}) :=
  f.local_meromorphic x

end MeromorphicFunction
