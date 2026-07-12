import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Fact 1.18: the basis criterion for continuity is already the canonical mathlib theorem
`TopologicalSpace.IsTopologicalBasis.continuous_iff`. It states that a map between topological
spaces is continuous exactly when the preimage of every basis element of the codomain is open. -/
recall TopologicalSpace.IsTopologicalBasis.continuous_iff
    {α : Type u} [TopologicalSpace α] {β : Type v} [TopologicalSpace β]
    {B : Set (Set β)} (hB : TopologicalSpace.IsTopologicalBasis B) {f : α → β} :
    Continuous f ↔ ∀ s ∈ B, IsOpen (f ⁻¹' s)
