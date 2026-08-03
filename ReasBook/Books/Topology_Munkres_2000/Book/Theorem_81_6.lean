module

public import Topology_Munkres_2000.Book.Definition_81_4.Regular
public import Topology_Munkres_2000.Book.Exercise_81_3.CoveringTransformation
import Topology_Munkres_2000.Book.Corollary_81_3.Normality
import Mathlib.Topology.Homeomorph.Lemmas

public section

open scoped HomeomorphGroup

universe u v

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B] [PathConnectedSpace B]
  [LocallyPathConnectedSpace B]

/-- Helper for Theorem 81.6: points in the same fiber of a regular connected covering are
related by a covering transformation. -/
private lemma exists_coveringTransformation_apply_eq_of_proj_eq
    (C : ConnectedCovering.{u} B) [C.IsRegular] {x y : C.Total}
    (hxy : C.proj x = C.proj y) :
    ∃ h : CoveringTransformation.group C.proj, h x = y := by
  -- Supply the connectedness carried by `C` to the fiber-transitivity theorem.
  letI : PathConnectedSpace C.Total := C.pathConnected
  letI : LocallyPathConnectedSpace C.Total := C.locallyPathConnected
  have hx_mem : x ∈ C.proj ⁻¹' {C.proj x} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hy_mem : y ∈ C.proj ⁻¹' {C.proj x} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxy.symm
  let xFiber : C.proj ⁻¹' {C.proj x} := ⟨x, hx_mem⟩
  let yFiber : C.proj ⁻¹' {C.proj x} := ⟨y, hy_mem⟩
  have hnormal :
      (C.isCoveringMap.fundamentalGroupMapRange (b₀ := C.proj x) rfl).Normal :=
    inferInstance
  -- Normality makes the covering-transformation action transitive on this fiber.
  have hfiberTransitive :=
    (C.isCoveringMap.fundamentalGroupMapRange_normal_iff_fiber_transitive
      C.proj x (C.proj x) rfl).mp hnormal
  obtain ⟨h, hh⟩ := hfiberTransitive xFiber yFiber
  exact ⟨h, hh⟩

/-- Helper for Theorem 81.6: the map induced on the orbit quotient of a regular connected
covering is injective. -/
private lemma quotientMap_injective (C : ConnectedCovering.{u} B) [C.IsRegular] :
    Function.Injective (CoveringTransformation.quotientMap C.proj) := by
  intro q₁ q₂ hq
  -- Choose representatives and reduce equality of quotient points to orbit membership.
  obtain ⟨x, rfl⟩ :=
    (HomeomorphGroup.isQuotientMap_mk (CoveringTransformation.group C.proj)).surjective q₁
  obtain ⟨y, rfl⟩ :=
    (HomeomorphGroup.isQuotientMap_mk (CoveringTransformation.group C.proj)).surjective q₂
  apply (HomeomorphGroup.mk_eq_mk_iff _).mpr
  apply (HomeomorphGroup.mem_orbit_iff _).mpr
  have hproj : C.proj x = C.proj y := by
    simpa only [CoveringTransformation.quotientMap_mk] using hq
  exact exists_coveringTransformation_apply_eq_of_proj_eq C hproj

/-- For a regular connected covering, the canonical map from the orbit quotient by all
covering transformations to the base is a homeomorphism. -/
theorem quotientMap_isHomeomorph (C : ConnectedCovering.{u} B) [C.IsRegular] :
    IsHomeomorph (CoveringTransformation.quotientMap C.proj) := by
  -- A surjective covering map is a quotient map; fiber transitivity supplies injectivity.
  letI : PathConnectedSpace C.Total := C.pathConnected
  letI : LocallyPathConnectedSpace C.Total := C.locallyPathConnected
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨?_, quotientMap_injective C⟩
  exact (CoveringTransformation.quotientMap_isCoveringMap
      C.proj C.isCoveringMap C.surjective).isQuotientMap
    (CoveringTransformation.quotientMap_surjective C.proj C.surjective)

/-- Theorem 81.6. A regular connected covering is homeomorphic over the base to the orbit
quotient by its full group of covering transformations. -/
theorem exists_quotientHomeomorph (C : ConnectedCovering.{u} B) [C.IsRegular] :
    ∃ k : C.Total / CoveringTransformation.group C.proj ≃ₜ B,
      C.proj = k ∘ HomeomorphGroup.mk (CoveringTransformation.group C.proj) := by
  -- Bundle the canonical quotient map and retain its defining factorization of `C.proj`.
  refine ⟨(quotientMap_isHomeomorph C).homeomorph _, ?_⟩
  funext x
  simpa only [Function.comp_apply, IsHomeomorph.homeomorph_apply] using
    congrFun (CoveringTransformation.quotientMap_comp_mk C.proj).symm x

end ConnectedCovering
