module

public import Topology_Munkres_2000.Book.Example_71_1.Earring

import all Topology_Munkres_2000.Book.Example_80_1
import Mathlib.Geometry.Manifold.Instances.Sphere

public section

open scoped Topology
open Filter

namespace InfiniteEarring

/-- Helper for Example 82.1: every component circle of the infinite earring is path connected. -/
private lemma isPathConnected_component (n : ℕ+) : IsPathConnected (component n) := by
  obtain ⟨e⟩ := componentHomeomorphicCircle n
  rw [isPathConnected_iff_pathConnectedSpace]
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

/-- The infinite earring in Example 82.1 is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace Space where
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

/-- Helper for Example 82.1: every component circle of the infinite earring is locally path
connected. -/
private lemma componentLocallyPathConnectedSpace (n : ℕ+) :
    LocallyPathConnectedSpace (component n) := by
  obtain ⟨e⟩ := componentHomeomorphicCircle n
  -- Transfer local path-connectedness from the circle's manifold charts along the homeomorphism.
  letI : LocallyPathConnectedSpace Circle :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  exact e.isOpenEmbedding.locallyPathConnectedSpace

/-- Helper for Example 82.1: away from the origin, a neighborhood's path component contains
an ambient neighborhood. -/
private lemma pathComponentIn_mem_nhds_of_ne_origin
    (x : Space) (hx : x ≠ origin) (u : Set Space) (hu : IsOpen u) (hxu : x ∈ u) :
    pathComponentIn u x ∈ nhds x := by
  obtain ⟨n, hxn⟩ := mem_carrier_iff (x : Plane) |>.mp x.property
  have hxcomponent : x ∈ component n := (mem_component_iff x n).mpr hxn
  let xComponent : component n := ⟨x, hxcomponent⟩
  have hlocal : LocallyPathConnectedSpace (component n) :=
    componentLocallyPathConnectedSpace n
  have huComponent : ((↑) : component n → Space) ⁻¹' u ∈ nhds xComponent :=
    (hu.preimage continuous_subtype_val).mem_nhds hxu
  have hpathComponent :
      pathComponentIn (((↑) : component n → Space) ⁻¹' u) xComponent ∈ nhds xComponent :=
    locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp hlocal xComponent
      (((↑) : component n → Space) ⁻¹' u)
      (hu.preimage continuous_subtype_val) hxu
  obtain ⟨v, hv, hvsub⟩ := (mem_nhds_subtype (component n) xComponent _).mp hpathComponent
  have hcomponentNhds : component n ∈ nhds x := by
    exact mem_interior_iff_mem_nhds.mp (mem_interior_component_of_ne_origin hxcomponent hx)
  refine mem_of_superset (inter_mem hv hcomponentNhds) ?_
  intro y hy
  let yComponent : component n := ⟨y, hy.2⟩
  have hyLocal :
      yComponent ∈ pathComponentIn (((↑) : component n → Space) ⁻¹' u) xComponent :=
    hvsub hy.1
  exact (hyLocal.map continuous_subtype_val).mono (Set.image_preimage_subset _ _)

/-- Helper for Example 82.1: at the origin, a neighborhood's path component contains an
ambient neighborhood. -/
private lemma pathComponentIn_mem_nhds_origin
    (u : Set Space) (hu : IsOpen u) (horigin : origin ∈ u) :
    pathComponentIn u origin ∈ nhds origin := by
  classical
  have huNhds : u ∈ nhds origin := hu.mem_nhds horigin
  obtain ⟨N, htail⟩ := Filter.eventually_atTop.mp (eventually_component_subset_nhds huNhds)
  have hcomponentNeighborhood (k : ℕ) :
      ∃ v ∈ nhds origin,
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
          nhds (componentOrigin (Nat.succPNat k)) :=
      locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mp hlocal
        (componentOrigin (Nat.succPNat k))
        (((↑) : component (Nat.succPNat k) → Space) ⁻¹' u)
        (hu.preimage continuous_subtype_val) horigin
    exact (mem_nhds_subtype (component (Nat.succPNat k))
      (componentOrigin (Nat.succPNat k)) _).mp hpathComponent
  choose v hv hvsub using hcomponentNeighborhood
  let w : Set Space := u ∩ ⋂ k ∈ Finset.range N, v k
  have hwNhds : w ∈ nhds origin := by
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

/-- The infinite earring in Example 82.1 is locally path connected. -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace Space := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  by_cases hx : x = origin
  · subst x
    exact pathComponentIn_mem_nhds_origin u hu hxu
  · exact pathComponentIn_mem_nhds_of_ne_origin x hx u hu hxu

end InfiniteEarring
