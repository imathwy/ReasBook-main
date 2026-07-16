import Mathlib
import StacksProject_2024.stacks_project.Chap17.Lemma_17_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ZeroObject
open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.9.5:
- primary domain: local vanishing of finite-type `\mathcal O_X`-modules from stalkwise vanishing on
  a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.moduleStalkMap`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `SheafOfModules.exists_open_neighborhood_epi_restriction_of_stalk_epi`;
- best owner abstraction: the ambient module category `RingedSpace.Modules X`, with local
  restriction expressed by `ℱ.over U` and the local epimorphism step delegated to the owner-level
  companion of Lemma `17.9.4`;
- primitive data: the module sheaf `ℱ`, the point `x`, and the vanishing hypothesis on the stalk
  module `RingedSpace.stalkModuleCat ℱ x`;
- derived API: the existence of an open neighbourhood on which the restriction `ℱ.over U` is zero.

Source/core/bridge triage:
- `source-facing`: the restriction of `ℱ` to some open neighbourhood of `x` is the zero sheaf;
- `core/canonical`: `IsZero (ℱ.over U)` in `RingedSpace.Modules`;
- `bridge/view`: applying the local epimorphism theorem to the zero morphism `0 ⟶ ℱ`. -/

-- Proof sketch: apply Lemma `17.9.4` to the zero morphism `0 ⟶ ℱ`; since the stalk module
-- `RingedSpace.stalkModuleCat ℱ x` is zero, the induced stalk morphism is an epimorphism and hence
-- surjective. Restricting the zero object remains zero, so a restricted epimorphism
-- `(0 : RingedSpace.Modules X).over U ⟶ ℱ.over U` forces `ℱ.over U` to be zero.
/-- Lemma 17.9.5: if `ℱ` is a finite type `\mathcal O_X`-module and the stalk `ℱ_x` is zero,
then there exists an open neighbourhood `U` of `x` such that the restriction `ℱ|_U` is the zero
sheaf. -/
theorem exists_open_neighborhood_restriction_isZero_of_stalk_isZero
    {X : RingedSpace.{u}} (ℱ : X.Modules)
    (x : X) [ℱ.IsFiniteType]
    (hℱx : IsZero (RingedSpace.stalkModuleCat ℱ x)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsZero (ℱ.over U) := by
  let φ : (0 : X.Modules) ⟶ ℱ := 0
  have hφx : Epi (RingedSpace.moduleStalkHom x φ) := hℱx.epi (RingedSpace.moduleStalkHom x φ)
  rcases
    SheafOfModules.exists_open_neighborhood_epi_restriction_of_stalk_epi
      φ x hφx with ⟨U, hxU, hU⟩
  let restriction : X.Modules ⥤ SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))
  letI : restriction.PreservesZeroMorphisms := ⟨fun _ _ ↦ by rfl⟩
  have hzero : IsZero ((0 : X.Modules).over U) := by
    simpa [restriction, SheafOfModules.over] using
      Functor.map_isZero restriction (isZero_zero (RingedSpace.Modules X))
  letI : Epi (φ |_ U) := hU
  exact ⟨U, hxU, IsZero.of_epi (φ |_ U) hzero⟩

end AlgebraicGeometry
