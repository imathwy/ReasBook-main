import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced `AlgebraicGeometry.Scheme.Modules.pushforward` and
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.
- Local Chapter 17 infrastructure already provides the ringed-space statements
  `ringedSpaceModulePushforward_isQuasicoherent_of_isClosedImmersion`,
  `RingedSpace.Hom.pushforward_exact_of_isClosedImmersion`,
  `RingedSpace.Hom.pushforward_fullyFaithful_of_isClosedImmersion`, and
  `RingedSpace.Hom.pushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedImmersion`.
-/

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

local notation "φi" => RingedSpace.Hom.toRingCatSheafHom i.toShHom
local notation "𝓘" => RingedSpace.closedImmersionIdealSheaf i.toShHom
local notation "ι𝓘" => kernel.ι (SheafOfModules.unitToPushforwardObjUnit φi)

/-- Lemma 29.4.1 (1): for a closed immersion `i : Z ⟶ X`, the pushforward of a quasi-coherent
`\mathcal O_Z`-module is quasi-coherent on `X`, so `i_*` is well-defined on quasi-coherent
modules. -/
@[stacks 01QY]
theorem pushforward_obj_isQuasicoherent_of_isClosedImmersion
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward i).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 29.4.1 (2): for a closed immersion `i : Z ⟶ X`, the pushforward functor on ambient
module sheaves is exact; together with part (1), this is the exactness of `i_*` on
quasi-coherent modules. -/
@[stacks 01QY]
theorem pushforward_exact_of_isClosedImmersion :
    exactFunctor Z.Modules X.Modules (Scheme.Modules.pushforward i) := sorry

/-- Lemma 29.4.1 (3): for a closed immersion `i : Z ⟶ X`, the pushforward functor on ambient
module sheaves is fully faithful; in particular its restriction to quasi-coherent modules is fully
faithful. -/
@[stacks 01QY, instance]
noncomputable instance pushforward_fullyFaithful_of_isClosedImmersion :
    (Scheme.Modules.pushforward i).FullyFaithful := sorry

/-- Lemma 29.4.1 (4): for a quasi-coherent `\mathcal O_X`-module `\mathcal G`, the module
`\mathcal G` lies in the essential image of `i_*` exactly when the ideal sheaf cutting out `Z`
acts trivially on all local sections of `\mathcal G`. -/
@[stacks 01QY]
theorem pushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedImmersion
    (𝒢 : X.Modules) [𝒢.IsQuasicoherent] :
    (Scheme.Modules.pushforward i).essImage 𝒢 ↔
      ∀ U : X.Opens,
        ∀ s : (𝓘).val.obj (op U),
        ∀ m : 𝒢.val.obj (op U),
          ((ι𝓘).val.app (op U) s) • m = 0 := sorry

/-- Companion for Lemma 29.4.1: for the adjunction `i^* ⊣ i_*`, membership in the essential image
of `i_*` is equivalent to the adjunction unit `\mathcal G \to i_* i^* \mathcal G` being an
isomorphism. -/
@[stacks 01QY]
theorem pushforward_essImage_iff_unit_isIso_of_isClosedImmersion
    (𝒢 : X.Modules) :
    (Scheme.Modules.pushforward i).essImage 𝒢 ↔
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app 𝒢) := sorry

end

end AlgebraicGeometry.Scheme.Modules
