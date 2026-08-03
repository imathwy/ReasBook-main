module

public import Topology_Munkres_2000.Book.Definition_80_1.Covering
public import Topology_Munkres_2000.Book.Example_71_1.Earring
public import Topology_Munkres_2000.Book.Remark_82_1.Classification

import all Topology_Munkres_2000.Book.Example_80_1
import Topology_Munkres_2000.Book.Lemma_80_4
import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
import all Topology_Munkres_2000.Book.Definition_80_1.Covering
import all Topology_Munkres_2000.Book.Definition_82_1.SemilocallySimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere

public section

open scoped Topology
open Filter

universe u v

namespace InfiniteEarring

/-- Helper for Example 82.1: every component circle of the infinite earring is path connected. -/
private lemma isPathConnected_component (n : ℕ+) : IsPathConnected (component n) := by
  obtain ⟨e⟩ := componentHomeomorphicCircle n
  rw [isPathConnected_iff_pathConnectedSpace]
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

/-- Helper for Example 82.1: every component circle of the infinite earring is locally path
connected. -/
private lemma componentLocallyPathConnectedSpace (n : ℕ+) :
    LocallyPathConnectedSpace (component n) := by
  obtain ⟨e⟩ := componentHomeomorphicCircle n
  -- Transfer local path-connectedness from the circle's manifold charts along the homeomorphism.
  letI : LocallyPathConnectedSpace Circle :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  exact e.isOpenEmbedding.locallyPathConnectedSpace

/-- Helper for Example 82.1: the infinite earring is path connected because its component
circles share the origin. -/
private theorem pathConnectedSpace : PathConnectedSpace Space where
  nonempty := ⟨origin⟩
  joined x y := by
    obtain ⟨m, hxm⟩ := mem_carrier_iff (x : Plane) |>.mp x.property
    obtain ⟨n, hyn⟩ := mem_carrier_iff (y : Plane) |>.mp y.property
    have hxcomponent : x ∈ component m := (mem_component_iff x m).mpr hxm
    have hycomponent : y ∈ component n := (mem_component_iff y n).mpr hyn
    exact ((isPathConnected_component m).joinedIn x hxcomponent origin
      (origin_mem_component m)).joined.trans
        ((isPathConnected_component n).joinedIn origin (origin_mem_component n) y
          hycomponent).joined

/-- Helper for Example 82.1: at a non-origin point, path components of neighborhoods contain
an ambient neighborhood. -/
private lemma pathComponentIn_mem_nhds_of_ne_origin
    (x : Space) (hx : x ≠ origin) (u : Set Space) (hu : IsOpen u) (hxu : x ∈ u) :
    pathComponentIn u x ∈ 𝓝 x := by
  obtain ⟨n, hxn⟩ := mem_carrier_iff (x : Plane) |>.mp x.property
  have hxcomponent : x ∈ component n := (mem_component_iff x n).mpr hxn
  let xComponent : component n := ⟨x, hxcomponent⟩
  have hlocal : LocallyPathConnectedSpace (component n) :=
    componentLocallyPathConnectedSpace n
  have huComponent : ((↑) : component n → Space) ⁻¹' u ∈ 𝓝 xComponent :=
    (hu.preimage continuous_subtype_val).mem_nhds hxu
  have hpathComponent :
      pathComponentIn (((↑) : component n → Space) ⁻¹' u) xComponent ∈ 𝓝 xComponent :=
    locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp hlocal xComponent
      (((↑) : component n → Space) ⁻¹' u)
      (hu.preimage continuous_subtype_val) hxu
  obtain ⟨v, hv, hvsub⟩ := (mem_nhds_subtype (component n) xComponent _).mp hpathComponent
  have hcomponentNhds : component n ∈ 𝓝 x := by
    exact mem_interior_iff_mem_nhds.mp (mem_interior_component_of_ne_origin hxcomponent hx)
  refine mem_of_superset (inter_mem hv hcomponentNhds) ?_
  intro y hy
  let yComponent : component n := ⟨y, hy.2⟩
  have hyLocal :
      yComponent ∈ pathComponentIn (((↑) : component n → Space) ⁻¹' u) xComponent :=
    hvsub hy.1
  exact (hyLocal.map continuous_subtype_val).mono (Set.image_preimage_subset _ _)

/-- Helper for Example 82.1: at the origin, path components of neighborhoods contain an
ambient neighborhood. -/
private lemma pathComponentIn_mem_nhds_origin
    (u : Set Space) (hu : IsOpen u) (horigin : origin ∈ u) :
    pathComponentIn u origin ∈ 𝓝 origin := by
  classical
  have huNhds : u ∈ 𝓝 origin := hu.mem_nhds horigin
  obtain ⟨N, htail⟩ := Filter.eventually_atTop.mp (eventually_component_subset_nhds huNhds)
  have hcomponentNeighborhood (k : ℕ) :
      ∃ v ∈ 𝓝 origin,
        ((↑) : component (Nat.succPNat k) → Space) ⁻¹' v ⊆
          pathComponentIn
            (((↑) : component (Nat.succPNat k) → Space) ⁻¹' u)
            (componentOrigin (Nat.succPNat k)) := by
    have hlocal : LocallyPathConnectedSpace (component (Nat.succPNat k)) :=
      componentLocallyPathConnectedSpace (Nat.succPNat k)
    have hpathComponent :
        pathComponentIn
            (((↑) : component (Nat.succPNat k) → Space) ⁻¹' u)
            (componentOrigin (Nat.succPNat k)) ∈
          𝓝 (componentOrigin (Nat.succPNat k)) :=
      locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp hlocal
        (componentOrigin (Nat.succPNat k))
        (((↑) : component (Nat.succPNat k) → Space) ⁻¹' u)
        (hu.preimage continuous_subtype_val) horigin
    exact (mem_nhds_subtype (component (Nat.succPNat k))
      (componentOrigin (Nat.succPNat k)) _).mp hpathComponent
  choose v hv hvsub using hcomponentNeighborhood
  let w : Set Space := u ∩ ⋂ k ∈ Finset.range N, v k
  have hwNhds : w ∈ 𝓝 origin := by
    exact inter_mem huNhds ((Filter.biInter_finset_mem (Finset.range N)).mpr
      (fun k _ ↦ hv k))
  refine mem_of_superset hwNhds ?_
  intro y hy
  obtain ⟨m, hym⟩ := mem_carrier_iff (y : Plane) |>.mp y.property
  have hycomponent : y ∈ component m := (mem_component_iff y m).mpr hym
  by_cases hm : m.natPred < N
  · have hyv : y ∈ v m.natPred := by
      exact Set.mem_iInter₂.mp hy.2 m.natPred (Finset.mem_range.mpr hm)
    let yComponent : component (Nat.succPNat m.natPred) :=
      ⟨y, PNat.succPNat_natPred m ▸ hycomponent⟩
    have hyLocal :
        yComponent ∈
          pathComponentIn
            (((↑) : component (Nat.succPNat m.natPred) → Space) ⁻¹' u)
            (componentOrigin (Nat.succPNat m.natPred)) :=
      hvsub m.natPred hyv
    exact (hyLocal.map continuous_subtype_val).mono (Set.image_preimage_subset _ _)
  · have hmge : N ≤ m.natPred := Nat.le_of_not_gt hm
    have hmSubset : component m ⊆ u := by
      simpa only [PNat.succPNat_natPred m] using htail m.natPred hmge
    exact ((isPathConnected_component m).joinedIn origin (origin_mem_component m) y
      hycomponent).mono hmSubset

/-- Helper for Example 82.1: the infinite earring is locally path connected. -/
private theorem locallyPathConnectedSpace : LocallyPathConnectedSpace Space := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  by_cases hx : x = origin
  · subst x
    exact pathComponentIn_mem_nhds_origin u hu hxu
  · exact pathComponentIn_mem_nhds_of_ne_origin x hx u hu hxu

attribute [local instance] pathConnectedSpace locallyPathConnectedSpace

/-- Helper for Example 82.1: the infinite earring has no universal covering. -/
theorem noUniversalCovering : ¬ Nonempty (UniversalCovering.{u} Space) := by
  -- A universal cover would make the earring semilocally simply connected by Lemma 80.4.
  rintro ⟨C⟩
  letI : SimplyConnectedSpace C.Total := C.simplyConnectedSpace
  have hsemilocallySimplyConnected : SemilocallySimplyConnectedSpace Space :=
    C.isCoveringMap.semilocallySimplyConnectedSpace_of_surjective C.surjective
  -- Its neighborhood at the origin contradicts Example 80.1's nontrivial inclusion map.
  obtain ⟨U, hU, hinclusion⟩ := hsemilocallySimplyConnected.exists_nhds origin
  unfold SemilocallySimplyConnectedSpace.point at hinclusion
  exact inclusionMap_ne_one U hU hinclusion

end InfiniteEarring

open scoped Pointwise

namespace Subgroup

/-- Helper for Example 82.1: a subgroup represents the bottom conjugacy class exactly when it
is the bottom subgroup. -/
private lemma mkConjClass_eq_bot_iff {G : Type*} [Group G] (H : Subgroup G) :
    mkConjClass H = mkConjClass (⊥ : Subgroup G) ↔ H = ⊥ := by
  constructor
  · intro hclass
    -- Cancel the conjugating automorphism after observing that it preserves the bottom subgroup.
    obtain ⟨g, hg⟩ := Subgroup.isConj_iff_exists.mp
      (Subgroup.mkConjClass_eq_iff.mp hclass)
    exact smul_left_cancel (MulAut.conj g)
      (hg.trans (Subgroup.smul_bot (MulAut.conj g)).symm)
  · intro hH
    -- Equal subgroups plainly determine equal quotient representatives.
    subst H
    rfl

end Subgroup

namespace MonoidHom

/-- Helper for Example 82.1: an injective group homomorphism with bottom range has a
subsingleton domain. -/
private lemma subsingleton_of_injective_range_eq_bot
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hinjective : Function.Injective f) (hrange : f.range = ⊥) : Subsingleton G := by
  -- Bottom range says that the homomorphism is the constant-one homomorphism.
  rw [MonoidHom.range_eq_bot_iff] at hrange
  constructor
  intro x y
  -- Injectivity now reduces the claim to equality of two values of the constant map.
  apply hinjective
  rw [hrange]
  simp only [MonoidHom.one_apply]

end MonoidHom

namespace ConnectedCovering

/-- Helper for Example 82.1: a connected covering classified by the bottom subgroup is a
universal covering map. -/
private lemma isUniversalCoveringMap_of_subgroupClass_eq_mkConjClass_bot
    {B : Type v} [TopologicalSpace B] (C : ConnectedCovering.{u} B) (b₀ : B)
    (hclass : C.subgroupClass b₀ =
      Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀))) :
    IsUniversalCoveringMap C.proj := by
  -- Choose a point above the base point and expose the concrete induced homomorphism range.
  obtain ⟨e₀, h₀⟩ := C.surjective b₀
  have hrangeClass :
      Subgroup.mkConjClass
          (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range =
        Subgroup.mkConjClass (⊥ : Subgroup (FundamentalGroup B b₀)) :=
    (C.subgroupClassAt_eq_mkConjClass b₀ e₀ h₀).symm.trans
      ((C.subgroupClass_mk b₀ e₀ h₀).symm.trans hclass)
  have hrange :
      (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range = ⊥ :=
    Subgroup.mkConjClass_eq_bot_iff
      (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀).range |>.mp
        hrangeClass
  -- Covering-map injectivity and trivial range make the upstairs fundamental group trivial.
  have hfundamentalGroup : Subsingleton (FundamentalGroup C.Total e₀) :=
    MonoidHom.subsingleton_of_injective_range_eq_bot
      (FundamentalGroup.mapOfEq ⟨C.proj, C.isCoveringMap.continuous⟩ h₀)
      (C.isCoveringMap.fundamentalGroupMap_injective h₀) hrange
  letI : PathConnectedSpace C.Total := C.pathConnectedSpace
  have hsimplyConnected : SimplyConnectedSpace C.Total :=
    (simplyConnectedSpace_iff_subsingleton_fundamentalGroup C.Total e₀).mpr
      hfundamentalGroup
  -- Reassemble the covering, surjectivity, and simple-connectedness fields.
  unfold IsUniversalCoveringMap
  exact ⟨C.isCoveringMap, C.surjective, hsimplyConnected⟩

end ConnectedCovering

namespace InfiniteEarring

/-- Example 82.1: The classification map from equivalence classes of connected coverings of
the infinite earring to conjugacy classes of subgroups of its fundamental group is not
surjective. -/
theorem classification_not_surjective :
    ¬ ConnectedCovering.IsClassificationSurjective.{u} origin := by
  intro hsurjective
  -- Surjectivity would realize the conjugacy class of the bottom subgroup.
  have hrealizesEveryClass :=
    (ConnectedCovering.isClassificationSurjective_iff origin).mp hsurjective
  obtain ⟨coveringClass, hclassification⟩ :=
    hrealizesEveryClass
      (Subgroup.mkConjClass
        (⊥ : Subgroup (FundamentalGroup Space origin)))
  obtain ⟨C, hrepresentative⟩ := Quotient.exists_rep coveringClass
  have hclassificationRepresentative :
      ConnectedCovering.classification Space origin
          (Quotient.mk (ConnectedCovering.equivalentSetoid Space) C) =
        Subgroup.mkConjClass
          (⊥ : Subgroup (FundamentalGroup Space origin)) :=
    (congrArg (ConnectedCovering.classification Space origin) hrepresentative).trans
      hclassification
  have hsubgroupClass :
      C.subgroupClass origin =
        Subgroup.mkConjClass
          (⊥ : Subgroup (FundamentalGroup Space origin)) :=
    (ConnectedCovering.classification_mk C origin).symm.trans
      hclassificationRepresentative
  -- The helper turns this representative into the forbidden universal cover.
  have huniversal : IsUniversalCoveringMap C.proj :=
    C.isUniversalCoveringMap_of_subgroupClass_eq_mkConjClass_bot origin hsubgroupClass
  exact noUniversalCovering
    (Nonempty.intro (UniversalCovering.of C.Total C.proj huniversal))

end InfiniteEarring
