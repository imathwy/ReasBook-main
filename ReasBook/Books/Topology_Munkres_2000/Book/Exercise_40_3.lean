module

public import Topology_Munkres_2000.Book.Exercise_36_4.PointFinite
public import Topology_Munkres_2000.Book.Definition_17_6

public section

universe u

namespace TopologicalSpace.IsTopologicalBasis

/-- Helper for Exercise 40.3: the basis core at `x` is the intersection of all
basis elements containing `x`. -/
private def basisCoreAt {X : Type u} (𝓑 : Set (Set X)) (x : X) : Set X :=
  ⋂ U ∈ {U : 𝓑 | x ∈ (U : Set X)}, (U : Set X)

/-- Helper for Exercise 40.3: in a `T₁` space, the basis core at a point is its
singleton. -/
private lemma basisCoreAt_eq_singleton {X : Type u} [TopologicalSpace X] [T1Space X]
    {𝓑 : Set (Set X)} (h𝓑 : IsTopologicalBasis 𝓑) (x : X) :
    basisCoreAt 𝓑 x = {x} := by
  classical
  -- Compare membership, using the `T₁` axiom to separate any other point from `x`.
  ext y
  constructor
  · intro hy
    by_contra hyx
    have hy_ne_x : y ≠ x := by
      simpa only [Set.mem_singleton_iff] using hyx
    have hx_compl : x ∈ ({y} : Set X)ᶜ := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy_ne_x.symm
    obtain ⟨U, hU_basis, hxU, hU_compl⟩ :=
      h𝓑.exists_subset_of_mem_open hx_compl isClosed_singleton.isOpen_compl
    have hy_all : ∀ V : 𝓑, x ∈ (V : Set X) → y ∈ (V : Set X) := by
      simpa only [basisCoreAt, Set.mem_iInter, Set.mem_setOf_eq] using hy
    have hyU : y ∈ U := by
      exact hy_all ⟨U, hU_basis⟩ hxU
    exact (hU_compl hyU) (Set.mem_singleton y)
  · intro hy
    -- The point `x` belongs to every basis element selected in its core.
    rw [Set.mem_singleton_iff] at hy
    subst y
    simp only [basisCoreAt, Set.mem_iInter, Set.mem_setOf_eq]
    intro U hxU
    exact hxU

/-- Helper for Exercise 40.3: a point-finite basis has an open basis core at
each point. -/
private lemma basisCoreAt_isOpen {X : Type u} [TopologicalSpace X]
    {𝓑 : Set (Set X)} (h𝓑 : IsTopologicalBasis 𝓑)
    (h_pointFinite : PointFinite (Subtype.val : 𝓑 → Set X)) (x : X) :
    IsOpen (basisCoreAt 𝓑 x) := by
  -- Point-finiteness makes the defining intersection finite, and basis elements are open.
  exact (h_pointFinite.finite x).isOpen_biInter fun U _ ↦ h𝓑.isOpen U.property

/-- A point-finite topological basis on a `T₁` space forces the topology to be discrete. -/
theorem discreteTopology_of_pointFinite {X : Type u} [TopologicalSpace X] [T1Space X]
    {𝓑 : Set (Set X)} (h𝓑 : IsTopologicalBasis 𝓑)
    (h_pointFinite : PointFinite (Subtype.val : 𝓑 → Set X)) :
    DiscreteTopology X := by
  -- Each singleton is the open core of the finitely many basis elements through its point.
  refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
  rw [← basisCoreAt_eq_singleton h𝓑 x]
  exact basisCoreAt_isOpen h𝓑 h_pointFinite x

/-- Exercise 40.3: A `T₁` space admitting a locally finite topological basis is
discrete. -/
theorem discreteTopology_of_locallyFinite {X : Type u} [TopologicalSpace X] [T1Space X]
    {𝓑 : Set (Set X)} (h𝓑 : IsTopologicalBasis 𝓑)
    (h_locallyFinite : LocallyFinite (Subtype.val : 𝓑 → Set X)) :
    DiscreteTopology X :=
  h𝓑.discreteTopology_of_pointFinite h_locallyFinite.toPointFinite

end TopologicalSpace.IsTopologicalBasis
