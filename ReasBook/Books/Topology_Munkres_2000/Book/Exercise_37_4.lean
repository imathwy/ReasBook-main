module

public import Topology_Munkres_2000.Book.Theorem_37_1.Quasicomponent
public import Topology_Munkres_2000.Book.Exercise_26_11
public import Mathlib.Order.Minimal
public import Mathlib.Order.Zorn

public section

open Set

universe u

/-- The closed subspaces in which `x` and `y` remain in the same quasicomponent. -/
def closedQuasicomponentSets {X : Type u} [TopologicalSpace X] (x y : X) : Set (Set X) :=
  {A | IsClosed A ∧ ∃ hx : x ∈ A, ∃ hy : y ∈ A,
    (⟨y, hy⟩ : A) ∈ quasicomponent (⟨x, hx⟩ : A)}


/-- A set belongs to `closedQuasicomponentSets x y` exactly when it is closed, contains both
points, and the corresponding subtype points belong to the same quasicomponent. -/
@[simp] theorem mem_closedQuasicomponentSets_iff {X : Type u} [TopologicalSpace X] {x y : X}
    {A : Set X} :
    A ∈ closedQuasicomponentSets x y ↔
      IsClosed A ∧ ∃ hx : x ∈ A, ∃ hy : y ∈ A,
        (⟨y, hy⟩ : A) ∈ quasicomponent (⟨x, hx⟩ : A) :=
  Iff.rfl

/- Exercise 37.4 (1): in a compact Hausdorff space, two points belong to the same
quasicomponent exactly when they belong to the same connected component. -/
#check sameQuasicomponent_iff_mem_connectedComponent

/-- Helper for Exercise 37.4: for a closed subspace, subtype quasicomponent membership is
ambient membership in the connected component inside that subspace. -/
private lemma mem_quasicomponent_subtype_iff_mem_connectedComponentIn
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A : Set X} (hA : IsClosed A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    ((⟨y, hy⟩ : A) ∈ quasicomponent (⟨x, hx⟩ : A)) ↔
      y ∈ connectedComponentIn A x := by
  -- Compactness of the closed subtype lets the global quasicomponent theorem apply there.
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  rw [sameQuasicomponent_iff_mem_connectedComponent]
  rw [connectedComponentIn_eq_image hx]
  -- Membership in the subtype component is exactly membership in its ambient image.
  constructor
  · intro hyComponent
    exact ⟨⟨y, hy⟩, hyComponent, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    subst y
    exact hz

/-- Helper for Exercise 37.4: the connected component of a point inside a closed set is
closed in the ambient space. -/
private lemma isClosed_connectedComponentIn_of_isClosed
    {X : Type u} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    {x : X} (hx : x ∈ A) : IsClosed (connectedComponentIn A x) := by
  -- Express the relative component as the image under the closed subtype embedding.
  rw [connectedComponentIn_eq_image hx]
  exact hA.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
    isClosed_connectedComponent

/-- Exercise 37.4 (2): the intersection of a chain of closed subspaces in which `x` and `y`
remain in the same quasicomponent is again such a closed subspace. -/
theorem sInter_mem_closedQuasicomponentSets {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x y : X} (hxy : y ∈ quasicomponent x)
    {𝓑 : Set (Set X)} (h𝓑 : 𝓑 ⊆ closedQuasicomponentSets x y)
    (hchain : IsChain (· ⊆ ·) 𝓑) :
    ⋂₀ 𝓑 ∈ closedQuasicomponentSets x y := by
  classical
  -- The empty intersection is the whole space, where the original hypothesis applies.
  by_cases h𝓑nonempty : 𝓑.Nonempty
  · let 𝓒 : Set (Set X) := (fun A : Set X ↦ connectedComponentIn A x) '' 𝓑
    have h𝓒nonempty : 𝓒.Nonempty := h𝓑nonempty.image _
    have h𝓒chain : IsChain (· ⊆ ·) 𝓒 := by
      exact hchain.image_of_map_rel (· ⊆ ·) (· ⊆ ·)
        (fun A : Set X ↦ connectedComponentIn A x)
        (fun A B hAB ↦ connectedComponentIn_mono x hAB)
    have h𝓒closed : ∀ C ∈ 𝓒, IsClosed C := by
      rintro C ⟨A, hA𝓑, rfl⟩
      obtain ⟨hAclosed, hxA, hyA, hxyA⟩ :=
        mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)
      exact isClosed_connectedComponentIn_of_isClosed hAclosed hxA
    have h𝓒preconnected : ∀ C ∈ 𝓒, IsPreconnected C := by
      rintro C ⟨A, hA𝓑, rfl⟩
      exact isPreconnected_connectedComponentIn
    have hpreconnected : IsPreconnected (⋂₀ 𝓒) :=
      isPreconnected_sInter_of_chain 𝓒 h𝓒nonempty h𝓒chain h𝓒closed h𝓒preconnected
    have hsInterClosed : IsClosed (⋂₀ 𝓑) := by
      apply isClosed_sInter
      intro A hA𝓑
      exact (mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)).1
    have hxInter : x ∈ ⋂₀ 𝓑 := by
      intro A hA𝓑
      exact (mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)).2.choose
    have hyInter : y ∈ ⋂₀ 𝓑 := by
      intro A hA𝓑
      exact (mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)).2.choose_spec.choose
    have hxComponents : x ∈ ⋂₀ 𝓒 := by
      intro C hC
      obtain ⟨A, hA𝓑, rfl⟩ := hC
      exact mem_connectedComponentIn
        (mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)).2.choose
    have hyComponents : y ∈ ⋂₀ 𝓒 := by
      intro C hC
      obtain ⟨A, hA𝓑, rfl⟩ := hC
      obtain ⟨hAclosed, hxA, hyA, hxyA⟩ :=
        mem_closedQuasicomponentSets_iff.mp (h𝓑 hA𝓑)
      exact (mem_quasicomponent_subtype_iff_mem_connectedComponentIn
        hAclosed hxA hyA).mp hxyA
    have hcomponentsSubset : ⋂₀ 𝓒 ⊆ ⋂₀ 𝓑 := by
      intro z hz A hA𝓑
      exact connectedComponentIn_subset A x (hz (connectedComponentIn A x) ⟨A, hA𝓑, rfl⟩)
    have hyComponentInter : y ∈ connectedComponentIn (⋂₀ 𝓑) x :=
      hpreconnected.subset_connectedComponentIn hxComponents hcomponentsSubset hyComponents
    -- The preconnected intersection lies in the relative component, which translates back to
    -- quasicomponent membership in the intersection subtype.
    rw [mem_closedQuasicomponentSets_iff]
    refine ⟨hsInterClosed, hxInter, hyInter, ?_⟩
    exact (mem_quasicomponent_subtype_iff_mem_connectedComponentIn
      hsInterClosed hxInter hyInter).mpr hyComponentInter
  · have h𝓑empty : 𝓑 = ∅ := not_nonempty_iff_eq_empty.mp h𝓑nonempty
    have hxUniv : x ∈ (univ : Set X) := trivial
    have hyUniv : y ∈ (univ : Set X) := trivial
    have hyComponentUniv : y ∈ connectedComponentIn (univ : Set X) x := by
      rw [connectedComponentIn_univ]
      exact sameQuasicomponent_iff_mem_connectedComponent.mp hxy
    rw [h𝓑empty, sInter_empty, mem_closedQuasicomponentSets_iff]
    refine ⟨isClosed_univ, hxUniv, hyUniv, ?_⟩
    exact (mem_quasicomponent_subtype_iff_mem_connectedComponentIn
      isClosed_univ hxUniv hyUniv).mpr hyComponentUniv

/-- Exercise 37.4 (3): the closed subspaces in which `x` and `y` remain in the same
quasicomponent have a minimal member. -/
theorem exists_minimal_closedQuasicomponentSet {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x y : X} (hxy : y ∈ quasicomponent x) :
    ∃ D : Set X, Minimal (fun A ↦ A ∈ closedQuasicomponentSets x y) D := by
  -- Every inclusion chain has its intersection as an admissible lower bound.
  refine zorn_superset (closedQuasicomponentSets x y) ?_
  intro 𝓑 h𝓑 hchain
  refine ⟨⋂₀ 𝓑, sInter_mem_closedQuasicomponentSets hxy h𝓑 hchain, ?_⟩
  intro A hA𝓑
  exact sInter_subset_of_mem hA𝓑

/-- Exercise 37.4 (4): a minimal closed subspace in which `x` and `y` remain in the same
quasicomponent is connected. -/
theorem isConnected_of_minimal_closedQuasicomponentSet {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x y : X} {D : Set X}
    (hD : Minimal (fun A ↦ A ∈ closedQuasicomponentSets x y) D) :
    IsConnected D := by
  obtain ⟨hDclosed, hxD, hyD, hxyD⟩ := mem_closedQuasicomponentSets_iff.mp hD.prop
  have hyComponent : y ∈ connectedComponentIn D x :=
    (mem_quasicomponent_subtype_iff_mem_connectedComponentIn
      hDclosed hxD hyD).mp hxyD
  have hxComponent : x ∈ connectedComponentIn D x := mem_connectedComponentIn hxD
  have hcomponentClosed : IsClosed (connectedComponentIn D x) :=
    isClosed_connectedComponentIn_of_isClosed hDclosed hxD
  have hcomponentAdmissible :
      connectedComponentIn D x ∈ closedQuasicomponentSets x y := by
    rw [mem_closedQuasicomponentSets_iff]
    refine ⟨hcomponentClosed, hxComponent, hyComponent, ?_⟩
    have hyNestedComponent :
        y ∈ connectedComponentIn (connectedComponentIn D x) x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        hxComponent Subset.rfl hyComponent
    exact (mem_quasicomponent_subtype_iff_mem_connectedComponentIn
      hcomponentClosed hxComponent hyComponent).mpr hyNestedComponent
  -- Minimality identifies `D` with its connected component containing `x`.
  have hD_eq_component : D = connectedComponentIn D x :=
    hD.eq_of_superset hcomponentAdmissible (connectedComponentIn_subset D x)
  rw [hD_eq_component]
  exact isConnected_connectedComponentIn_iff.mpr hxD
