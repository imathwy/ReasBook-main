module

public import Topology_Munkres_2000.Book.Definition_71_2
public import Mathlib.Topology.Coherent

public section

universe u v

namespace Topology

namespace IsCoherentWith

/-- Helper for Definition 71.2: a finite closed cover is coherent with the ambient topology. -/
theorem of_finite_closed_cover {ι : Type v} [Finite ι]
    {X : Type u} [TopologicalSpace X] {S : ι → Set X}
    (h_closed : ∀ i, IsClosed (S i)) (h_cover : ⋃ i, S i = Set.univ) :
    IsCoherentWith (Set.range S) := by
  -- Test closedness on the cover, then reconstruct the set as a finite union of intersections.
  refine of_isClosed fun t ht ↦ ?_
  rw [← Set.univ_inter t, ← h_cover, Set.iUnion_inter]
  refine isClosed_iUnion_of_finite fun i ↦ ?_
  -- Relative closedness becomes ambient closedness because each member of the cover is closed.
  have h_relative : IsClosed (((↑) ⁻¹' t : Set (S i))) := ht (S i) ⟨i, rfl⟩
  simpa only [Subtype.image_preimage_coe] using h_relative.trans (h_closed i)

end IsCoherentWith

namespace IsFiniteWedgeOfCircles

variable {ι : Type v} [Fintype ι] {X : Type u} [TopologicalSpace X]
  {S : ι → Set X} {p : X}

/-- The finite-wedge property is equivalent to its Hausdorff, covering, circle, and
intersection conditions. -/
theorem iff :
    IsFiniteWedgeOfCircles S p ↔
      T2Space X ∧ (⋃ i, S i = Set.univ) ∧
        (∀ i, Nonempty (S i ≃ₜ Circle)) ∧ Pairwise (fun i j ↦ S i ∩ S j = {p}) :=
  ⟨fun h ↦ ⟨h.t2Space, h.covers, h.homeomorphic_circle, h.inter_eq⟩,
    fun h ↦ {
      covers := h.2.1
      homeomorphic_circle := h.2.2.1
      inter_eq := h.2.2.2
      t2Space := h.1 }⟩

/-- Explicit finite circle-wedge conditions construct the corresponding property. -/
theorem of [T2Space X]
    (h_cover : ⋃ i, S i = Set.univ)
    (h_circle : ∀ i, Nonempty (S i ≃ₜ Circle))
    (h_inter : Pairwise (fun i j ↦ S i ∩ S j = {p})) :
    IsFiniteWedgeOfCircles S p :=
  { covers := h_cover
    homeomorphic_circle := h_circle
    inter_eq := h_inter
    t2Space := inferInstance }

/-- Helper for Definition 71.2: every member of a finite circle wedge is compact. -/
theorem isCompact [IsFiniteWedgeOfCircles S p] (i : ι) : IsCompact (S i) := by
  -- Transfer compactness of `Circle` across the supplied homeomorphism.
  obtain ⟨e⟩ := IsCircleUnion.homeomorphic_circle (S := S) (p := p) i
  exact isCompact_iff_compactSpace.mpr e.symm.compactSpace

/-- Every circle in a finite wedge is closed in the ambient Hausdorff space. -/
theorem isClosed [IsFiniteWedgeOfCircles S p] (i : ι) : IsClosed (S i) := by
  -- Install the stored Hausdorff structure, so compactness implies closedness.
  letI : T2Space X := IsFiniteWedgeOfCircles.t2Space (S := S) (p := p)
  exact (isCompact (S := S) (p := p) i).isClosed

/-- The ambient topology of a finite wedge is coherent with its family of circles. -/
theorem isCoherentWith (h : IsFiniteWedgeOfCircles S p) :
    Topology.IsCoherentWith (Set.range S) := by
  -- View the wedge hypothesis as a local instance and apply finite closed-cover coherence.
  letI : IsFiniteWedgeOfCircles S p := h
  exact IsCoherentWith.of_finite_closed_cover
    (fun i ↦ isClosed (S := S) (p := p) i) h.covers

/-- The specified wedge point belongs to every circle. -/
theorem mem_basepoint [IsFiniteWedgeOfCircles S p] (i : ι) : p ∈ S i := by
  -- Choose one circle containing the basepoint from the covering condition.
  have hp_union : p ∈ ⋃ j, S j := by
    rw [IsCircleUnion.covers (S := S) (p := p)]
    exact Set.mem_univ p
  obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp_union
  classical
  by_cases hij : i = j
  · simpa only [hij] using hpj
  · -- For distinct indices, the pairwise intersection is the basepoint singleton.
    have hp_inter : p ∈ S i ∩ S j := by
      rw [IsCircleUnion.inter_eq (S := S) (p := p) hij]
      exact Set.mem_singleton p
    exact hp_inter.1

end IsFiniteWedgeOfCircles

end Topology

end
