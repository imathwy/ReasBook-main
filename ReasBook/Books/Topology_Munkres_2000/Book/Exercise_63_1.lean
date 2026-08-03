module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Theorem_59_3
public import Topology_Munkres_2000.Book.Theorem_63_3
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.SetTheory.Cardinal.Basic

public section

open Set

/-- Helper for Exercise 63.1: a simple closed curve is compact in its ambient space. -/
private lemma isCompact_simpleClosedCurve
    {X : Type*} [TopologicalSpace X] (C : Set X)
    [Topology.IsSimpleClosedCurve C] : IsCompact C := by
  -- Transfer compactness from the circle across the specified homeomorphism.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Helper for Exercise 63.1: a simple closed curve is connected in its ambient space. -/
private lemma isConnected_simpleClosedCurve
    {X : Type*} [TopologicalSpace X] (C : Set X)
    [Topology.IsSimpleClosedCurve C] : IsConnected C := by
  -- Transfer connectedness from the circle and then map the full subtype into the ambient space.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : ConnectedSpace C := e.connectedSpace_iff.mpr inferInstance
  have hC : IsConnected (Set.univ : Set C) := isConnected_univ
  have himage : ((fun x : C ↦ x.1) '' Set.univ) = C := by
    rw [Set.image_univ, Subtype.range_coe]
  rw [← himage]
  exact hC.image Subtype.val continuous_subtype_val.continuousOn

/-- Helper for Exercise 63.1: when a subspace has exactly two components, a
chosen component and the other component are disjoint and cover the subspace. -/
private lemma exists_otherComponent_partition
    {X : Type*} [TopologicalSpace X] (F : Set X)
    (hF : Cardinal.mk (ConnectedComponents F) = 2) (x : F) :
    ∃ y : F, Disjoint (connectedComponentIn F x) (connectedComponentIn F y) ∧
      connectedComponentIn F x ∪ connectedComponentIn F y = F := by
  classical
  -- Select the unique quotient component different from the component of `x`.
  obtain ⟨q, hqx, hqunique⟩ :=
    (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hF
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
  have hxy : (x : ConnectedComponents F) ≠ y := hqx.symm
  have hcomponentDisjoint : Disjoint (connectedComponent x) (connectedComponent y) := by
    exact connectedComponent_disjoint (ConnectedComponents.coe_ne_coe.mp hxy)
  refine ⟨y, ?_, ?_⟩
  · -- Injectivity of the subtype inclusion preserves disjointness of the two components.
    rw [connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2]
    exact Set.disjoint_image_of_injective Subtype.val_injective hcomponentDisjoint
  · -- Every point has either the chosen quotient class or the unique other class.
    apply Set.Subset.antisymm
    · exact union_subset (connectedComponentIn_subset F x) (connectedComponentIn_subset F y)
    · intro z hzF
      let zF : F := ⟨z, hzF⟩
      by_cases hzx : (zF : ConnectedComponents F) = x
      · left
        rw [connectedComponentIn_eq_image x.2]
        exact ⟨zF, ConnectedComponents.coe_eq_coe'.mp hzx, rfl⟩
      · right
        have hzy : (zF : ConnectedComponents F) = y := hqunique _ hzx
        rw [connectedComponentIn_eq_image y.2]
        exact ⟨zF, ConnectedComponents.coe_eq_coe'.mp hzy, rfl⟩

/-- Helper for Exercise 63.1: the frontier of a union of two disjoint closed
sets is the union of their frontiers. -/
private lemma frontier_union_eq_of_isClosed_of_disjoint
    {X : Type*} [TopologicalSpace X] (D₁ D₂ : Set X)
    (hD₁ : IsClosed D₁) (hD₂ : IsClosed D₂) (hdisjoint : Disjoint D₁ D₂) :
    frontier (D₁ ∪ D₂) = frontier D₁ ∪ frontier D₂ := by
  have hclosureDisjoint : Disjoint (closure D₁) (closure D₂) := by
    rwa [hD₁.closure_eq, hD₂.closure_eq]
  have hinterior : interior (D₁ ∪ D₂) = interior D₁ ∪ interior D₂ :=
    interior_union_of_disjoint_closure hclosureDisjoint
  apply Set.Subset.antisymm
  · -- A frontier point of the closed union lies in one closed summand.
    intro x hx
    have hxUnion : x ∈ D₁ ∪ D₂ := (hD₁.union hD₂).frontier_subset hx
    have hxNotInterior : x ∉ interior (D₁ ∪ D₂) :=
      (mem_frontier_iff_notMem_interior hxUnion).mp hx
    rcases hxUnion with hxD₁ | hxD₂
    · exact Or.inl ((mem_frontier_iff_notMem_interior hxD₁).mpr
        (fun hxInterior ↦ hxNotInterior (interior_mono subset_union_left hxInterior)))
    · exact Or.inr ((mem_frontier_iff_notMem_interior hxD₂).mpr
        (fun hxInterior ↦ hxNotInterior (interior_mono subset_union_right hxInterior)))
  · -- Disjointness rules out the other summand's interior at each frontier point.
    intro x hx
    rcases hx with hxD₁ | hxD₂
    · have hxMem : x ∈ D₁ := hD₁.frontier_subset hxD₁
      have hxUnionMem : x ∈ D₁ ∪ D₂ := Or.inl hxMem
      apply (mem_frontier_iff_notMem_interior hxUnionMem).mpr
      rw [hinterior]
      intro hxInterior
      rcases hxInterior with hxInterior | hxInterior
      · exact (mem_frontier_iff_notMem_interior hxMem).mp hxD₁ hxInterior
      · exact Set.disjoint_left.mp hdisjoint hxMem (interior_subset hxInterior)
    · have hxMem : x ∈ D₂ := hD₂.frontier_subset hxD₂
      have hxUnionMem : x ∈ D₁ ∪ D₂ := Or.inr hxMem
      apply (mem_frontier_iff_notMem_interior hxUnionMem).mpr
      rw [hinterior]
      intro hxInterior
      rcases hxInterior with hxInterior | hxInterior
      · exact Set.disjoint_left.mp hdisjoint (interior_subset hxInterior) hxMem
      · exact (mem_frontier_iff_notMem_interior hxMem).mp hxD₂ hxInterior

/-- Helper for Exercise 63.1: a relatively clopen preconnected subset is the
connected component of any one of its points. -/
private lemma connectedComponentIn_eq_of_isPreconnected_isClopen
    {X : Type*} [TopologicalSpace X] {F U : Set X}
    (hUF : U ⊆ F) (hU : IsPreconnected U)
    (hclopen : IsClopen (Subtype.val ⁻¹' U : Set F)) {x : X} (hx : x ∈ U) :
    connectedComponentIn F x = U := by
  apply Set.Subset.antisymm
  · -- Relative clopenness traps the subtype component inside `U`.
    rw [connectedComponentIn_eq_image (hUF hx)]
    rintro y ⟨yF, hyF, rfl⟩
    exact hclopen.connectedComponent_subset hx hyF
  · -- Preconnectedness gives the reverse maximality inclusion.
    exact hU.subset_connectedComponentIn hx hUF

/-- Helper for Exercise 63.1: one side of a disjoint open two-set partition is
clopen in the subtype being partitioned. -/
private lemma isClopen_preimage_of_disjoint_open_partition
    {X : Type*} [TopologicalSpace X] {F U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hdisjoint : Disjoint U V) (hcover : F = U ∪ V) :
    IsClopen (Subtype.val ⁻¹' U : Set F) := by
  have hcompl : (Subtype.val ⁻¹' U : Set F)ᶜ = Subtype.val ⁻¹' V := by
    ext x
    have hxCover : x.1 ∈ U ∪ V := hcover ▸ x.2
    simp only [Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · exact fun hxU ↦ hxCover.resolve_left hxU
    · exact fun hxV hxU ↦ Set.disjoint_left.mp hdisjoint hxU hxV
  refine ⟨?_, hUopen.preimage continuous_subtype_val⟩
  -- The displayed complement is open, hence the first side is relatively closed.
  rw [← isOpen_compl_iff, hcompl]
  exact hVopen.preimage continuous_subtype_val

/-- Helper for Exercise 63.1: two disjoint Jordan curves admit three disjoint
open connected complementary regions with the prescribed frontiers. -/
private lemma disjointJordanCurves_complementRegions
    (C₁ C₂ : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C₁] [Topology.IsSimpleClosedCurve C₂]
    (hdisjoint : Disjoint C₁ C₂) :
    ∃ W₁ W₂ W₃ : Set (StandardSphere 2),
      IsOpen W₁ ∧ IsOpen W₂ ∧ IsOpen W₃ ∧
      IsConnected W₁ ∧ IsConnected W₂ ∧ IsConnected W₃ ∧
      Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₂ W₃ ∧
      (C₁ ∪ C₂)ᶜ = W₁ ∪ W₂ ∪ W₃ ∧
      frontier W₁ = C₁ ∧ frontier W₂ = C₂ ∧ frontier W₃ = C₁ ∪ C₂ := by
  classical
  letI : LocallyPathConnectedSpace (StandardSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  have hC₁connected : IsConnected C₁ := isConnected_simpleClosedCurve C₁
  have hC₂connected : IsConnected C₂ := isConnected_simpleClosedCurve C₂
  obtain ⟨c₁, hc₁⟩ := hC₁connected.nonempty
  obtain ⟨c₂, hc₂⟩ := hC₂connected.nonempty
  have hC₁subset : C₁ ⊆ C₂ᶜ := by
    intro x hxC₁ hxC₂
    exact Set.disjoint_left.mp hdisjoint hxC₁ hxC₂
  have hC₂subset : C₂ ⊆ C₁ᶜ := by
    intro x hxC₂ hxC₁
    exact Set.disjoint_left.mp hdisjoint hxC₁ hxC₂
  let c₁' : (C₂ᶜ : Set (StandardSphere 2)) := ⟨c₁, hC₁subset hc₁⟩
  let c₂' : (C₁ᶜ : Set (StandardSphere 2)) := ⟨c₂, hC₂subset hc₂⟩
  have htwo₁ : Cardinal.mk (ConnectedComponents (C₁ᶜ : Set (StandardSphere 2))) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C₁)
  have htwo₂ : Cardinal.mk (ConnectedComponents (C₂ᶜ : Set (StandardSphere 2))) = 2 :=
    Set.separatesInto_iff.mp (jordanCurveSphere_separatesInto C₂)
  obtain ⟨w₁, hparts₁, hcover₁⟩ := exists_otherComponent_partition C₁ᶜ htwo₁ c₂'
  obtain ⟨w₂, hparts₂, hcover₂⟩ := exists_otherComponent_partition C₂ᶜ htwo₂ c₁'
  let A₁ : Set (StandardSphere 2) := connectedComponentIn C₁ᶜ c₂'
  let W₁ : Set (StandardSphere 2) := connectedComponentIn C₁ᶜ w₁
  let A₂ : Set (StandardSphere 2) := connectedComponentIn C₂ᶜ c₁'
  let W₂ : Set (StandardSphere 2) := connectedComponentIn C₂ᶜ w₂
  change Disjoint A₁ W₁ at hparts₁
  change A₁ ∪ W₁ = C₁ᶜ at hcover₁
  change Disjoint A₂ W₂ at hparts₂
  change A₂ ∪ W₂ = C₂ᶜ at hcover₂
  have hC₂A₁ : C₂ ⊆ A₁ := by
    -- Connectedness places the whole second curve in the side containing `c₂`.
    exact hC₂connected.2.subset_connectedComponentIn hc₂ hC₂subset
  have hC₁A₂ : C₁ ⊆ A₂ := by
    -- Symmetrically, the first curve lies in the chosen side of the second complement.
    exact hC₁connected.2.subset_connectedComponentIn hc₁ hC₁subset
  have hC₁closed : IsClosed C₁ := (isCompact_simpleClosedCurve C₁).isClosed
  have hC₂closed : IsClosed C₂ := (isCompact_simpleClosedCurve C₂).isClosed
  have hA₁open : IsOpen A₁ := hC₁closed.isOpen_compl.connectedComponentIn
  have hW₁open : IsOpen W₁ := hC₁closed.isOpen_compl.connectedComponentIn
  have hA₂open : IsOpen A₂ := hC₂closed.isOpen_compl.connectedComponentIn
  have hW₂open : IsOpen W₂ := hC₂closed.isOpen_compl.connectedComponentIn
  have hA₁connected : IsConnected A₁ :=
    isConnected_connectedComponentIn_iff.mpr c₂'.2
  have hW₁connected : IsConnected W₁ :=
    isConnected_connectedComponentIn_iff.mpr w₁.2
  have hA₂connected : IsConnected A₂ :=
    isConnected_connectedComponentIn_iff.mpr c₁'.2
  have hW₂connected : IsConnected W₂ :=
    isConnected_connectedComponentIn_iff.mpr w₂.2
  have hfrontierA₁ : frontier A₁ = C₁ :=
    jordanCurveSphere_frontier_component C₁ c₂'
  have hfrontierW₁ : frontier W₁ = C₁ :=
    jordanCurveSphere_frontier_component C₁ w₁
  have hfrontierA₂ : frontier A₂ = C₂ :=
    jordanCurveSphere_frontier_component C₂ c₁'
  have hfrontierW₂ : frontier W₂ = C₂ :=
    jordanCurveSphere_frontier_component C₂ w₂
  have hclosureW₁ : closure W₁ = W₁ ∪ C₁ := by
    -- Normalize the first closure once through its Jordan frontier.
    rw [closure_eq_self_union_frontier, hfrontierW₁]
  have hclosureW₂ : closure W₂ = W₂ ∪ C₂ := by
    -- Normalize the second closure in the same stable form.
    rw [closure_eq_self_union_frontier, hfrontierW₂]
  have hW₁subsetC₂compl : W₁ ⊆ C₂ᶜ := by
    intro x hxW₁ hxC₂
    exact Set.disjoint_left.mp hparts₁ (hC₂A₁ hxC₂) hxW₁
  have hW₂subsetC₁compl : W₂ ⊆ C₁ᶜ := by
    intro x hxW₂ hxC₁
    exact Set.disjoint_left.mp hparts₂ (hC₁A₂ hxC₁) hxW₂
  have hW₁subsetA₂ : W₁ ⊆ A₂ := by
    -- The open component `A₂` meets `W₁` at the latter's frontier.
    have hc₁A₂ : c₁ ∈ A₂ := hC₁A₂ hc₁
    have hc₁closureW₁ : c₁ ∈ closure W₁ := by
      exact frontier_subset_closure (hfrontierW₁.symm ▸ hc₁)
    obtain ⟨z, hzA₂, hzW₁⟩ :=
      (mem_closure_iff.mp hc₁closureW₁) A₂ hA₂open hc₁A₂
    have hsubset := hW₁connected.2.subset_connectedComponentIn hzW₁ hW₁subsetC₂compl
    have heq : A₂ = connectedComponentIn C₂ᶜ z := connectedComponentIn_eq hzA₂
    rwa [← heq] at hsubset
  have hW₂subsetA₁ : W₂ ⊆ A₁ := by
    -- The symmetric frontier argument places `W₂` in `A₁`.
    have hc₂A₁ : c₂ ∈ A₁ := hC₂A₁ hc₂
    have hc₂closureW₂ : c₂ ∈ closure W₂ := by
      exact frontier_subset_closure (hfrontierW₂.symm ▸ hc₂)
    obtain ⟨z, hzA₁, hzW₂⟩ :=
      (mem_closure_iff.mp hc₂closureW₂) A₁ hA₁open hc₂A₁
    have hsubset := hW₂connected.2.subset_connectedComponentIn hzW₂ hW₂subsetC₁compl
    have heq : A₁ = connectedComponentIn C₁ᶜ z := connectedComponentIn_eq hzA₁
    rwa [← heq] at hsubset
  have hW₁W₂ : Disjoint W₁ W₂ :=
    hparts₂.mono hW₁subsetA₂ Subset.rfl
  have hW₁C₂ : Disjoint W₁ C₂ :=
    Set.disjoint_left.mpr (fun _ hxW hxC ↦ hW₁subsetC₂compl hxW hxC)
  have hC₁W₂ : Disjoint C₁ W₂ :=
    Set.disjoint_left.mpr (fun _ hxC hxW ↦ hW₂subsetC₁compl hxW hxC)
  have hclosuresDisjoint : Disjoint (closure W₁) (closure W₂) := by
    -- The four pairwise disjoint pieces make the two normalized closures disjoint.
    rw [hclosureW₁, hclosureW₂]
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hW₁W₂, hW₁C₂⟩,
      disjoint_union_right.mpr ⟨hC₁W₂, hdisjoint⟩⟩
  have hcomplClosureW₁ : (closure W₁)ᶜ = A₁ := by
    -- The complementary Jordan side is exactly the complement of the other side's closure.
    ext x
    rw [hclosureW₁]
    constructor
    · intro hx
      have hxC₁ : x ∈ C₁ᶜ := fun hxC ↦ hx (Or.inr hxC)
      rcases hcover₁.symm ▸ hxC₁ with hxA₁ | hxW₁
      · exact hxA₁
      · exact (hx (Or.inl hxW₁)).elim
    · intro hxA₁ hxClosure
      rcases hxClosure with hxW₁ | hxC₁
      · exact Set.disjoint_left.mp hparts₁ hxA₁ hxW₁
      · exact connectedComponentIn_subset C₁ᶜ c₂' hxA₁ hxC₁
  have hcomplClosureW₂ : (closure W₂)ᶜ = A₂ := by
    -- The same partition identity holds for the second curve.
    ext x
    rw [hclosureW₂]
    constructor
    · intro hx
      have hxC₂ : x ∈ C₂ᶜ := fun hxC ↦ hx (Or.inr hxC)
      rcases hcover₂.symm ▸ hxC₂ with hxA₂ | hxW₂
      · exact hxA₂
      · exact (hx (Or.inl hxW₂)).elim
    · intro hxA₂ hxClosure
      rcases hxClosure with hxW₂ | hxC₂
      · exact Set.disjoint_left.mp hparts₂ hxA₂ hxW₂
      · exact connectedComponentIn_subset C₂ᶜ c₁' hxA₂ hxC₂
  have hclosureW₁nonseparating : ¬ (closure W₁).Separates := by
    -- Its complement is the connected region `A₁`.
    intro hseparates
    apply Set.separates_iff.mp hseparates
    apply isPreconnected_iff_preconnectedSpace.mp
    rw [hcomplClosureW₁]
    exact hA₁connected.2
  have hclosureW₂nonseparating : ¬ (closure W₂).Separates := by
    -- Its complement is the connected region `A₂`.
    intro hseparates
    apply Set.separates_iff.mp hseparates
    apply isPreconnected_iff_preconnectedSpace.mp
    rw [hcomplClosureW₂]
    exact hA₂connected.2
  have hinterSimplyConnected : IsSimplyConnected ((closure W₁ ∩ closure W₂)ᶜ) := by
    -- Disjoint closures reduce the intersection complement to the full simply connected sphere.
    have hdimension : 2 ≤ 2 := by
      norm_num
    rw [Set.disjoint_iff_inter_eq_empty.mp hclosuresDisjoint, compl_empty]
    exact ((Homeomorph.Set.univ (StandardSphere 2)).toHomotopyEquiv.simplyConnectedSpace_iff).mpr
      (simplyConnectedSpace_standardSphere 2 hdimension)
  have hunionNonseparating : ¬ (closure W₁ ∪ closure W₂).Separates :=
    union_not_separates_of_compl_inter_simplyConnected
      (closure W₁) (closure W₂) isClosed_closure isClosed_closure
      hinterSimplyConnected hclosureW₁nonseparating hclosureW₂nonseparating
  let W₃ : Set (StandardSphere 2) := (closure W₁ ∪ closure W₂)ᶜ
  have hW₃open : IsOpen W₃ := (isClosed_closure.union isClosed_closure).isOpen_compl
  have hW₃preconnected : IsPreconnected W₃ := by
    -- Nonseparation is precisely preconnectedness of this complement.
    apply isPreconnected_iff_preconnectedSpace.mpr
    by_contra hpreconnected
    exact hunionNonseparating (Set.separates_iff.mpr hpreconnected)
  have hW₃nonempty : W₃.Nonempty := by
    -- Near `c₁`, the side `A₁` supplies a point outside both closed outer regions.
    have hc₁closureA₁ : c₁ ∈ closure A₁ := by
      exact frontier_subset_closure (hfrontierA₁.symm ▸ hc₁)
    have hc₁closureW₁ : c₁ ∈ closure W₁ := by
      exact frontier_subset_closure (hfrontierW₁.symm ▸ hc₁)
    have hc₁notClosureW₂ : c₁ ∉ closure W₂ :=
      fun hc₁W₂ ↦ Set.disjoint_left.mp hclosuresDisjoint hc₁closureW₁ hc₁W₂
    obtain ⟨z, hzNotW₂, hzA₁⟩ := (mem_closure_iff.mp hc₁closureA₁)
      (closure W₂)ᶜ isClosed_closure.isOpen_compl hc₁notClosureW₂
    have hzNotW₁ : z ∉ closure W₁ := by
      have hzCompl : z ∈ (closure W₁)ᶜ := by
        rw [hcomplClosureW₁]
        exact hzA₁
      exact hzCompl
    exact ⟨z, fun hzUnion ↦ hzUnion.elim hzNotW₁ hzNotW₂⟩
  have hW₃connected : IsConnected W₃ := ⟨hW₃nonempty, hW₃preconnected⟩
  have hW₁W₃ : Disjoint W₁ W₃ := by
    exact Set.disjoint_left.mpr (fun _ hxW₁ hxW₃ ↦
      hxW₃ (Or.inl (subset_closure hxW₁)))
  have hW₂W₃ : Disjoint W₂ W₃ := by
    exact Set.disjoint_left.mpr (fun _ hxW₂ hxW₃ ↦
      hxW₃ (Or.inr (subset_closure hxW₂)))
  have hcover : (C₁ ∪ C₂)ᶜ = W₁ ∪ W₂ ∪ W₃ := by
    -- Points off the curves either lie in an outer region or avoid both normalized closures.
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxW₁ : x ∈ W₁
      · exact Or.inl (Or.inl hxW₁)
      · by_cases hxW₂ : x ∈ W₂
        · exact Or.inl (Or.inr hxW₂)
        · right
          intro hxClosures
          rcases hxClosures with hxClosureW₁ | hxClosureW₂
          · rw [hclosureW₁] at hxClosureW₁
            exact hxClosureW₁.elim hxW₁ (fun hxC₁ ↦ hx (Or.inl hxC₁))
          · rw [hclosureW₂] at hxClosureW₂
            exact hxClosureW₂.elim hxW₂ (fun hxC₂ ↦ hx (Or.inr hxC₂))
    · intro x hxRegions
      rcases hxRegions with hxOuter | hxW₃
      · rcases hxOuter with hxW₁ | hxW₂
        · intro hxCurves
          rcases hxCurves with hxC₁ | hxC₂
          · exact connectedComponentIn_subset C₁ᶜ w₁ hxW₁ hxC₁
          · exact hW₁subsetC₂compl hxW₁ hxC₂
        · intro hxCurves
          rcases hxCurves with hxC₁ | hxC₂
          · exact hW₂subsetC₁compl hxW₂ hxC₁
          · exact connectedComponentIn_subset C₂ᶜ w₂ hxW₂ hxC₂
      · intro hxCurves
        rcases hxCurves with hxC₁ | hxC₂
        · exact hxW₃ (Or.inl (hclosureW₁.symm ▸ Or.inr hxC₁))
        · exact hxW₃ (Or.inr (hclosureW₂.symm ▸ Or.inr hxC₂))
  have hfrontierClosureW₁ : frontier (closure W₁) = C₁ := by
    -- Compare the closed side with its complementary connected side.
    calc
      frontier (closure W₁) = frontier (closure W₁)ᶜ := (frontier_compl _).symm
      _ = frontier A₁ := congrArg frontier hcomplClosureW₁
      _ = C₁ := hfrontierA₁
  have hfrontierClosureW₂ : frontier (closure W₂) = C₂ := by
    -- The same complementary-side comparison computes the second closed frontier.
    calc
      frontier (closure W₂) = frontier (closure W₂)ᶜ := (frontier_compl _).symm
      _ = frontier A₂ := congrArg frontier hcomplClosureW₂
      _ = C₂ := hfrontierA₂
  have hfrontierW₃ : frontier W₃ = C₁ ∪ C₂ := by
    -- Frontier commutes with this complement and with the disjoint closed union.
    calc
      frontier W₃ = frontier (closure W₁ ∪ closure W₂) := frontier_compl _
      _ = frontier (closure W₁) ∪ frontier (closure W₂) :=
        frontier_union_eq_of_isClosed_of_disjoint _ _ isClosed_closure isClosed_closure
          hclosuresDisjoint
      _ = C₁ ∪ C₂ := congrArg₂ Set.union hfrontierClosureW₁ hfrontierClosureW₂
  exact ⟨W₁, W₂, W₃, hW₁open, hW₂open, hW₃open,
    hW₁connected, hW₂connected, hW₃connected, hW₁W₂, hW₁W₃,
    hW₂W₃, hcover, hfrontierW₁, hfrontierW₂, hfrontierW₃⟩

/-- Helper for Exercise 63.1: the complementary components of two disjoint
Jordan curves are indexed by `Fin 3`. -/
private lemma disjointJordanCurves_componentEquiv
    (C₁ C₂ : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C₁] [Topology.IsSimpleClosedCurve C₂]
    (hdisjoint : Disjoint C₁ C₂) :
    Nonempty (ConnectedComponents ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2)) ≃ Fin 3) := by
  classical
  obtain ⟨W₁, W₂, W₃, hW₁open, hW₂open, hW₃open,
    hW₁connected, hW₂connected, hW₃connected, hW₁W₂, hW₁W₃, hW₂W₃,
    hcover, hfrontierW₁, hfrontierW₂, hfrontierW₃⟩ :=
      disjointJordanCurves_complementRegions C₁ C₂ hdisjoint
  let F : Set (StandardSphere 2) := (C₁ ∪ C₂)ᶜ
  have hW₁subset : W₁ ⊆ F := by
    unfold F
    rw [hcover]
    exact subset_union_left.trans subset_union_left
  have hW₂subset : W₂ ⊆ F := by
    unfold F
    rw [hcover]
    exact subset_union_right.trans subset_union_left
  have hW₃subset : W₃ ⊆ F := by
    unfold F
    rw [hcover]
    exact subset_union_right
  have hW₁clopen : IsClopen (Subtype.val ⁻¹' W₁ : Set F) := by
    -- The other two open regions form the relative complement of `W₁`.
    apply isClopen_preimage_of_disjoint_open_partition hW₁open
      (hW₂open.union hW₃open)
      (disjoint_union_right.mpr ⟨hW₁W₂, hW₁W₃⟩)
    unfold F
    rw [hcover]
    ac_rfl
  have hW₂clopen : IsClopen (Subtype.val ⁻¹' W₂ : Set F) := by
    -- Reorder the same partition to isolate `W₂`.
    apply isClopen_preimage_of_disjoint_open_partition hW₂open
      (hW₁open.union hW₃open)
      (disjoint_union_right.mpr ⟨hW₁W₂.symm, hW₂W₃⟩)
    unfold F
    rw [hcover]
    ac_rfl
  have hW₃clopen : IsClopen (Subtype.val ⁻¹' W₃ : Set F) := by
    -- Finally isolate the middle region from the two outer regions.
    apply isClopen_preimage_of_disjoint_open_partition hW₃open
      (hW₁open.union hW₂open)
      (disjoint_union_right.mpr ⟨hW₁W₃.symm, hW₂W₃.symm⟩)
    unfold F
    rw [hcover]
    ac_rfl
  have connectedPreimage {W : Set (StandardSphere 2)}
      (hWsubset : W ⊆ F) (hWconnected : IsConnected W) :
      IsConnected (Subtype.val ⁻¹' W : Set F) := by
    -- The subtype inclusion identifies the relative region with its ambient image.
    constructor
    · obtain ⟨w, hw⟩ := hWconnected.nonempty
      exact ⟨⟨w, hWsubset hw⟩, hw⟩
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hWsubset]
      exact hWconnected.2
  have hW₁relativeConnected : IsConnected (Subtype.val ⁻¹' W₁ : Set F) :=
    connectedPreimage hW₁subset hW₁connected
  have hW₂relativeConnected : IsConnected (Subtype.val ⁻¹' W₂ : Set F) :=
    connectedPreimage hW₂subset hW₂connected
  have hW₃relativeConnected : IsConnected (Subtype.val ⁻¹' W₃ : Set F) :=
    connectedPreimage hW₃subset hW₃connected
  let U : Fin 3 → Set F := ![
    Subtype.val ⁻¹' W₁,
    Subtype.val ⁻¹' W₂,
    Subtype.val ⁻¹' W₃]
  have hUclopen : ∀ i, IsClopen (U i) := by
    intro i
    fin_cases i
    · simpa [U] using hW₁clopen
    · simpa [U] using hW₂clopen
    · simpa [U] using hW₃clopen
  have hUconnected : ∀ i, IsConnected (U i) := by
    intro i
    fin_cases i
    · simpa [U] using hW₁relativeConnected
    · simpa [U] using hW₂relativeConnected
    · simpa [U] using hW₃relativeConnected
  have hUdisjoint : Pairwise (Function.onFun Disjoint U) := by
    -- Ambient disjointness pulls back to all unequal pairs of relative regions.
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (Subtype.val ⁻¹' W₁ : Set F) (Subtype.val ⁻¹' W₂ : Set F)
      exact Disjoint.preimage Subtype.val hW₁W₂
    · change Disjoint (Subtype.val ⁻¹' W₁ : Set F) (Subtype.val ⁻¹' W₃ : Set F)
      exact Disjoint.preimage Subtype.val hW₁W₃
    · change Disjoint (Subtype.val ⁻¹' W₂ : Set F) (Subtype.val ⁻¹' W₁ : Set F)
      exact Disjoint.preimage Subtype.val hW₁W₂.symm
    · exact (hij rfl).elim
    · change Disjoint (Subtype.val ⁻¹' W₂ : Set F) (Subtype.val ⁻¹' W₃ : Set F)
      exact Disjoint.preimage Subtype.val hW₂W₃
    · change Disjoint (Subtype.val ⁻¹' W₃ : Set F) (Subtype.val ⁻¹' W₁ : Set F)
      exact Disjoint.preimage Subtype.val hW₁W₃.symm
    · change Disjoint (Subtype.val ⁻¹' W₃ : Set F) (Subtype.val ⁻¹' W₂ : Set F)
      exact Disjoint.preimage Subtype.val hW₂W₃.symm
    · exact (hij rfl).elim
  have hUcover : ⋃ i, U i = Set.univ := by
    -- The ambient three-region cover gives a witness index for every subtype point.
    apply eq_univ_of_forall
    intro x
    have hxRegions : x.1 ∈ W₁ ∪ W₂ ∪ W₃ := hcover ▸ x.2
    rcases hxRegions with hxOuter | hxW₃
    · rcases hxOuter with hxW₁ | hxW₂
      · apply Set.mem_iUnion.mpr
        refine ⟨0, ?_⟩
        simpa [U]
      · apply Set.mem_iUnion.mpr
        refine ⟨1, ?_⟩
        simpa [U]
    · apply Set.mem_iUnion.mpr
      refine ⟨2, ?_⟩
      simpa [U]
  -- The canonical clopen-partition equivalence supplies the desired component index.
  exact ⟨ConnectedComponents.equivOfIsClopenOfIsConnected
    hUclopen hUdisjoint hUcover hUconnected⟩

/-- Exercise 63.1 (1): Two disjoint simple closed curves in the standard
two-sphere separate it into exactly three components. -/
theorem disjointJordanCurves_separatesInto
    (C₁ C₂ : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C₁] [Topology.IsSimpleClosedCurve C₂]
    (hdisjoint : Disjoint C₁ C₂) :
    (C₁ ∪ C₂).SeparatesInto 3 := by
  -- The three-region decomposition gives the required finite component index.
  rw [Set.separatesInto_iff, Cardinal.mk_eq_nat_iff]
  exact disjointJordanCurves_componentEquiv C₁ C₂ hdisjoint

/-- Companion to Exercise 63.1 (2): The frontiers of the three complementary components
of two disjoint simple closed curves are the curves and their union. -/
theorem disjointJordanCurves_frontier_range
    (C₁ C₂ : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve C₁] [Topology.IsSimpleClosedCurve C₂]
    (hdisjoint : Disjoint C₁ C₂) :
    Set.range (fun x : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2)) ↦
      frontier (connectedComponentIn (C₁ ∪ C₂)ᶜ x)) = {C₁, C₂, C₁ ∪ C₂} := by
  obtain ⟨W₁, W₂, W₃, hW₁open, hW₂open, hW₃open,
    hW₁connected, hW₂connected, hW₃connected, hW₁W₂, hW₁W₃, hW₂W₃,
    hcover, hfrontierW₁, hfrontierW₂, hfrontierW₃⟩ :=
      disjointJordanCurves_complementRegions C₁ C₂ hdisjoint
  have hW₁subset : W₁ ⊆ (C₁ ∪ C₂)ᶜ := by
    rw [hcover]
    exact subset_union_left.trans subset_union_left
  have hW₂subset : W₂ ⊆ (C₁ ∪ C₂)ᶜ := by
    rw [hcover]
    exact subset_union_right.trans subset_union_left
  have hW₃subset : W₃ ⊆ (C₁ ∪ C₂)ᶜ := by
    rw [hcover]
    exact subset_union_right
  have hW₁clopen :
      IsClopen (Subtype.val ⁻¹' W₁ : Set ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) := by
    -- In the complement subtype, the other two open regions are the complement of `W₁`.
    apply isClopen_preimage_of_disjoint_open_partition hW₁open
      (hW₂open.union hW₃open)
      (disjoint_union_right.mpr ⟨hW₁W₂, hW₁W₃⟩)
    rw [hcover]
    ac_rfl
  have hW₂clopen :
      IsClopen (Subtype.val ⁻¹' W₂ : Set ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) := by
    -- Reorder the partition to obtain relative clopenness of `W₂`.
    apply isClopen_preimage_of_disjoint_open_partition hW₂open
      (hW₁open.union hW₃open)
      (disjoint_union_right.mpr ⟨hW₁W₂.symm, hW₂W₃⟩)
    rw [hcover]
    ac_rfl
  have hW₃clopen :
      IsClopen (Subtype.val ⁻¹' W₃ : Set ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) := by
    -- The same relative partition isolates the middle region.
    apply isClopen_preimage_of_disjoint_open_partition hW₃open
      (hW₁open.union hW₂open)
      (disjoint_union_right.mpr ⟨hW₁W₃.symm, hW₂W₃.symm⟩)
    rw [hcover]
    ac_rfl
  have hcomponentW₁
      (x : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) (hx : x.1 ∈ W₁) :
      connectedComponentIn (C₁ ∪ C₂)ᶜ x = W₁ := by
    -- Relative clopenness and connectedness identify the first region with the component of `x`.
    exact connectedComponentIn_eq_of_isPreconnected_isClopen
      hW₁subset hW₁connected.2 hW₁clopen hx
  have hcomponentW₂
      (x : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) (hx : x.1 ∈ W₂) :
      connectedComponentIn (C₁ ∪ C₂)ᶜ x = W₂ := by
    -- Apply the same component adapter to the second outer region.
    exact connectedComponentIn_eq_of_isPreconnected_isClopen
      hW₂subset hW₂connected.2 hW₂clopen hx
  have hcomponentW₃
      (x : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2))) (hx : x.1 ∈ W₃) :
      connectedComponentIn (C₁ ∪ C₂)ᶜ x = W₃ := by
    -- Apply the adapter once more to the middle region.
    exact connectedComponentIn_eq_of_isPreconnected_isClopen
      hW₃subset hW₃connected.2 hW₃clopen hx
  apply Set.Subset.antisymm
  · -- Every complement point lies in one of the three regions, so its frontier is listed.
    rintro D ⟨x, rfl⟩
    have hxRegions : x.1 ∈ W₁ ∪ W₂ ∪ W₃ := hcover ▸ x.2
    rcases hxRegions with hxOuter | hxW₃
    · rcases hxOuter with hxW₁ | hxW₂
      · dsimp only
        rw [hcomponentW₁ x hxW₁, hfrontierW₁]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · dsimp only
        rw [hcomponentW₂ x hxW₂, hfrontierW₂]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · dsimp only
      rw [hcomponentW₃ x hxW₃, hfrontierW₃]
      exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))))
  · -- A point chosen in each nonempty connected region realizes its listed frontier.
    intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with hD | hD
    · subst D
      obtain ⟨w₁, hw₁⟩ := hW₁connected.nonempty
      let x₁ : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2)) := ⟨w₁, hW₁subset hw₁⟩
      refine ⟨x₁, ?_⟩
      dsimp only
      rw [hcomponentW₁ x₁ hw₁, hfrontierW₁]
    · rcases hD with hD | hD
      · subst D
        obtain ⟨w₂, hw₂⟩ := hW₂connected.nonempty
        let x₂ : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2)) := ⟨w₂, hW₂subset hw₂⟩
        refine ⟨x₂, ?_⟩
        dsimp only
        rw [hcomponentW₂ x₂ hw₂, hfrontierW₂]
      · subst D
        obtain ⟨w₃, hw₃⟩ := hW₃connected.nonempty
        let x₃ : ((C₁ ∪ C₂)ᶜ : Set (StandardSphere 2)) := ⟨w₃, hW₃subset hw₃⟩
        refine ⟨x₃, ?_⟩
        dsimp only
        rw [hcomponentW₃ x₃ hw₃, hfrontierW₃]
