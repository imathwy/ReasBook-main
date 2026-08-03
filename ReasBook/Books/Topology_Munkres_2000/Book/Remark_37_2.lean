module

public import Topology_Munkres_2000.Book.Theorem_26_9

public section

open Set

universe u

/-- Remark 37.2. The members of a family with the finite intersection property need not
be closed: in a compact space, the intersection of their closures is nonempty. -/
theorem CompactSpace.iInter_closure_nonempty {X : Type u} [TopologicalSpace X]
    [CompactSpace X] (𝒜 : Set (Set X)) (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    (⋂ A ∈ 𝒜, closure A).Nonempty := by
  have h := compactSpace_iff_closed_finiteIntersectionProperty X |>.mp inferInstance
    (closure '' 𝒜) (fun _ hA ↦ hA.choose_spec.2 ▸ isClosed_closure) h𝒜.closure
  simpa only [sInter_image] using h
