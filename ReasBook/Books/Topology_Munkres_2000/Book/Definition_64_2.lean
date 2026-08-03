module

public import Topology_Munkres_2000.Book.Definition_64_2.ThetaSpace

public section

/- Definition 64.2: A theta space is a Hausdorff union of three arcs meeting pairwise
exactly at their common endpoints. -/
#check Topology.IsThetaSpace

universe u v

namespace Topology.IsThetaSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Definition 64.2: Being a theta space is invariant under homeomorphism. -/
theorem homeomorph_iff (e : X ≃ₜ Y) : IsThetaSpace X ↔ IsThetaSpace Y := by
  constructor
  · intro h
    -- Transport Hausdorffness and the chosen presentation from the source to the target.
    letI : T2Space X := h.toT2Space
    letI : T2Space Y := e.t2Space
    obtain ⟨P⟩ := h.presentation
    obtain ⟨Q⟩ := P.nonempty_of_homeomorph e
    exact ofPresentation Q
  · intro h
    -- Apply the same construction to the inverse homeomorphism for the reverse implication.
    letI : T2Space Y := h.toT2Space
    letI : T2Space X := e.symm.t2Space
    obtain ⟨P⟩ := h.presentation
    obtain ⟨Q⟩ := P.nonempty_of_homeomorph e.symm
    exact ofPresentation Q

end Topology.IsThetaSpace
