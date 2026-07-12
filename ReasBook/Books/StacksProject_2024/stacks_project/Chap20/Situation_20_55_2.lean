import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap18.LocalSectionMul

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open TopologicalSpace
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Situation 20.55.2:
- primary domain: ideal sheaves on a ringed space, expressed canonically as subobjects of the
  structure-module sheaf and restricted to opens, together with multiplication by local sections
  on restricted module sheaves;
- inspected owner declarations of the same kind:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CategoryTheory.Subobject.restrict`,
  `RingedSpace.Modules`,
  `SheafOfModules.unit`,
  `SheafOfModules.over`,
  `SheafOfModules.localSectionMul`,
  `RingedSpace.moduleRestrictionMap`;
- best owner abstraction: the source-facing primitive datum is the canonical ideal sheaf
  `I : Subobject 𝒪X`, with inclusion `I.arrow`; its restrictions are expressed through
  `SheafOfModules.over` on the underlying module `I` and the restriction notation
  `I.arrow |_ U`, while local multiplication is owned by
  `SheafOfModules.localSectionMul X.sheaf`;
- primitive data: an ideal sheaf `I : Subobject 𝒪X`;
- derived API: only the source-facing local principal regularity predicate below. The monicity of
  `I.arrow` is already canonical `Subobject` API, so no local duplicate bridge should remain.

Source/core/bridge triage:
- `source-facing`: the local principal regular ideal condition from Situation `20.55.2`;
- `core/canonical`: `Subobject 𝒪X`, `Subobject.arrow`, `Subobject.restrict`,
  `RingedSpace.Modules X`, `SheafOfModules.unit`, `SheafOfModules.over`,
  `SheafOfModules.localSectionMul`, and the restriction notation `|_`;
- `bridge/view`: none beyond the direct use of `I.arrow` on the owner surface. -/

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/-- Situation 20.55.2: around each point, the ideal sheaf inclusion is identified with
multiplication by a local section whose multiplication map on the restricted structure sheaf is
monomorphic. -/
@[stacks 0GT4]
class SatisfiesLocallyPrincipalRegularIdealCondition
    (I : Subobject 𝒪X) : Prop where
  /-- A locally principal ideal chart exists around every point. The corresponding multiplication
  map is automatically monomorphic because it identifies with the restricted subobject inclusion
  through an isomorphism. -/
  exists_chart (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ∃ (e : SheafOfModules.over I U ≅ SheafOfModules.over 𝒪X U)
        (s : X.presheaf.obj (op U)),
        e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
          I.arrow |_ U

namespace SatisfiesLocallyPrincipalRegularIdealCondition

/-- Helper for Situation `20.55.2`: the restricted inclusion of a subobject remains
monomorphic. -/
theorem restrictArrow_mono {I : Subobject 𝒪X} (U : Opens X) :
    Mono (I.arrow |_ U) := by
  -- Restriction is functorial, so it preserves the monomorphism of the subobject arrow.
  let F := SheafOfModules.pushforward (𝟙 (Sheaf.over X.ringCatSheaf U))
  let _ : F.PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape F
  change Mono (F.map I.arrow)
  infer_instance

/-- On a chart from Situation `20.55.2`, the local multiplication map is monomorphic because its
composite with the chart isomorphism is the restricted ideal-sheaf inclusion. -/
instance localSectionMul_mono {I : Subobject 𝒪X} {U : Opens X}
    (e : SheafOfModules.over I U ≅ SheafOfModules.over 𝒪X U)
    (s : X.presheaf.obj (op U))
    (he :
      e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
        I.arrow |_ U) :
    Mono (SheafOfModules.localSectionMul X.sheaf 𝒪X U s) := by
  -- The restricted ideal-sheaf inclusion is mono because it is the restriction of a subobject arrow.
  have hmono_restrict : Mono (I.arrow |_ U) := restrictArrow_mono U
  -- The chart identifies the composite with that restricted inclusion.
  have hcomp : Mono (e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s) := by
    exact he ▸ hmono_restrict
  -- Cancel the chart isomorphism on the left to recover monicity of the multiplication map.
  exact (mono_comp_iff_of_isIso e.hom _).1 hcomp

/-- On a chart from Situation `20.55.2`, the local multiplication map is monomorphic because its
composite with the chart isomorphism is the restricted ideal-sheaf inclusion. -/
theorem mono_localSectionMul {I : Subobject 𝒪X} {U : Opens X}
    (e : SheafOfModules.over I U ≅ SheafOfModules.over 𝒪X U)
    (s : X.presheaf.obj (op U))
    (he :
      e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s =
        I.arrow |_ U) :
    Mono (SheafOfModules.localSectionMul X.sheaf 𝒪X U s) := by
  exact localSectionMul_mono e s he

/-- Around every point, Situation `20.55.2` provides a principal chart whose generator acts
regularly on the restricted structure sheaf. -/
theorem exists_chart_with_mono_localSectionMul {I : Subobject 𝒪X}
    [hprincipal : SatisfiesLocallyPrincipalRegularIdealCondition I] (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ∃ e : SheafOfModules.over I U ≅ SheafOfModules.over 𝒪X U,
      ∃ s : X.presheaf.obj (op U),
        (e.hom ≫ SheafOfModules.localSectionMul X.sheaf 𝒪X U s = I.arrow |_ U) ∧
          Mono (SheafOfModules.localSectionMul X.sheaf 𝒪X U s) := by
  -- Unpack the source-facing chart and append the derived monomorphism conclusion.
  obtain ⟨U, hxU, e, s, he⟩ := hprincipal.exists_chart x
  exact ⟨U, hxU, e, s, he, mono_localSectionMul e s he⟩

end SatisfiesLocallyPrincipalRegularIdealCondition

/- Situation `20.55.2` is expressed by the primitive source-facing class
`SatisfiesLocallyPrincipalRegularIdealCondition I` on the canonical ideal-sheaf owner
`I : Subobject 𝒪X`; the monomorphism of `I.arrow` is intrinsic `Subobject` API, so no parallel
local data field or `Fact` wrapper belongs here. The chartwise monomorphism of
`localSectionMul` is publicized as the canonical instance
`SatisfiesLocallyPrincipalRegularIdealCondition.localSectionMul_mono`, with
`SatisfiesLocallyPrincipalRegularIdealCondition.mono_localSectionMul` as a companion theorem. -/

end AlgebraicGeometry.RingedSpace
