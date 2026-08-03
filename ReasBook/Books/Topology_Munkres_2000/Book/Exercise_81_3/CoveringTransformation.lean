module

public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Topology_Munkres_2000.Book.Definition_81_6.ProperlyDiscontinuous
public import Topology_Munkres_2000.Book.Proposition_81_2.Covering
public import Topology_Munkres_2000.Book.Theorem_81_5
public import Topology_Munkres_2000.Book.Lemma_80_2
public import Mathlib.Topology.Covering.Basic

public section

open scoped HomeomorphGroup

universe u v

namespace CoveringTransformation

variable {X : Type u} {B : Type v} [TopologicalSpace X] [TopologicalSpace B]

/-- Helper for Exercise 81.3: a covering transformation of a preconnected covering that fixes a
point is the identity. -/
lemma eq_one_of_smul_eq [PreconnectedSpace X] (p : X → B) (hp : IsCoveringMap p)
    (g : group p) (x : X) (hfixed : g • x = x) : g = 1 := by
  -- Uniqueness of lifts identifies the transformation with the identity map.
  have hcomp : p ∘ (g : X ≃ₜ X) = p ∘ (1 : X ≃ₜ X) := by
    funext y
    exact map_smul p g y
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun
    (hp.eq_of_comp_eq (g : X ≃ₜ X).continuous continuous_id hcomp x hfixed)

/-- The full covering-transformation group of a covering map with path-connected total space acts
properly discontinuously. -/
theorem properlyDiscontinuousMulAction_of_isCoveringMap [PathConnectedSpace X]
    (p : X → B) (hp : IsCoveringMap p) :
    ProperlyDiscontinuousMulAction (group p) X := by
  -- Use one locally injective covering chart as the disjointness neighborhood.
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hp.isLocalHomeomorph.isLocallyInjective x
  refine ⟨U, hUopen.mem_nhds hxU, fun g hg ↦ Set.disjoint_left.mpr ?_⟩
  intro y hytranslate hyU
  obtain ⟨z, hzU, rfl⟩ := hytranslate
  -- A point in both sets would give a fixed point, forcing `g = 1`.
  have hfixed : g • z = z := hUinj hyU hzU (map_smul p g z)
  exact hg (eq_one_of_smul_eq p hp g z hfixed)

/-- The full covering-transformation group of a connected covering acts properly discontinuously. -/
instance properlyDiscontinuousMulAction (C : ConnectedCovering.{u} B) :
    ProperlyDiscontinuousMulAction (group C.proj) C.Total := by
  -- Install the path-connectedness stored in the bundled covering, then use the general result.
  letI : PathConnectedSpace C.Total := C.pathConnected
  exact properlyDiscontinuousMulAction_of_isCoveringMap C.proj C.isCoveringMap

/-- A map takes equal values at points related by the orbit relation of its covering
transformations. -/
theorem map_eq_of_orbitRel {X : Type u} {B : Type v} (p : X → B) {x y : X}
    [TopologicalSpace X] (hxy : MulAction.orbitRel (group p) X x y) : p x = p y := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hxy
  exact (congrArg p hg.symm).trans (map_smul p g y)

/-- The canonical map from the orbit quotient by all covering transformations to the base. -/
def quotientMap {X : Type u} {B : Type v} [TopologicalSpace X]
    (p : X → B) : X / group p → B :=
  Quotient.lift p fun _ _ hxy ↦ map_eq_of_orbitRel p hxy

/-- The canonical quotient map agrees with `p` on representatives. -/
theorem quotientMap_mk {X : Type u} {B : Type v} [TopologicalSpace X]
    (p : X → B) (x : X) :
    quotientMap p (HomeomorphGroup.mk (group p) x) = p x := by
  -- Reduce the named orbit projection to the quotient constructor computation rule.
  rw [HomeomorphGroup.mk_eq_quotient_mk]
  simp only [quotientMap, Quotient.lift_mk]

/-- The induced map on the covering-transformation orbit quotient factors `p` through the orbit
projection. -/
theorem quotientMap_comp_mk {X : Type u} {B : Type v} [TopologicalSpace X] (p : X → B) :
    quotientMap p ∘ HomeomorphGroup.mk (group p) = p := by
  -- Check the factorization on each representative.
  funext x
  exact quotientMap_mk p x

/-- Helper for Exercise 81.3: continuity descends to the map induced on the orbit quotient. -/
lemma quotientMap_continuous {X : Type u} {B : Type v} [TopologicalSpace X]
    [TopologicalSpace B] (p : X → B) (hp : Continuous p) :
    Continuous (quotientMap p) := by
  -- Apply the universal property of the quotient and use the named factorization equation.
  apply (HomeomorphGroup.isQuotientMap_mk (group p)).continuous_iff.mpr
  rw [quotientMap_comp_mk]
  exact hp

/-- For a surjective covering with connected, locally connected source data, the map induced on
the covering-transformation orbit quotient is a covering map. -/
theorem quotientMap_isCoveringMap [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [LocallyConnectedSpace B] (p : X → B) (hp : IsCoveringMap p)
    (hp_surjective : Function.Surjective p) : IsCoveringMap (quotientMap p) := by
  -- Proper discontinuity makes the orbit projection a covering map.
  have hprojection : IsCoveringMap (HomeomorphGroup.mk (group p)) :=
    (HomeomorphGroup.isCoveringMap_iff_properlyDiscontinuous (group p)).mpr
      (properlyDiscontinuousMulAction_of_isCoveringMap p hp)
  -- Cancel that projection from the covering factorization.
  exact (coveringMap_of_comp_left (quotientMap_continuous p hp.continuous)
    (quotientMap_comp_mk p).symm hp hp_surjective hprojection
    (HomeomorphGroup.isQuotientMap_mk (group p)).surjective).1

/-- If `p` is surjective, then its induced map on the covering-transformation orbit quotient is
surjective. -/
theorem quotientMap_surjective {X : Type u} {B : Type v} [TopologicalSpace X]
    (p : X → B) (hp : Function.Surjective p) :
    Function.Surjective (quotientMap p) := by
  -- Lift a preimage of the base point to its orbit class.
  intro b
  obtain ⟨x, rfl⟩ := hp b
  exact ⟨HomeomorphGroup.mk (group p) x, quotientMap_mk p x⟩

end CoveringTransformation
