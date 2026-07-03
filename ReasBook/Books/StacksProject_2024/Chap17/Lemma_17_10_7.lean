import Mathlib
import stacks_project.Chap17.Definition_17_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.10.7:
- primary domain: pullback of associated module sheaves on ringed spaces, together with scalar
  extension on global-sections modules;
- sampled owner declarations:
  `associatedModuleSheaf`,
  `RingedSpace.Hom.pullback`,
  `ModuleCat.extendScalars`,
  `SheafOfModules.pullbackComp`;
- best owner abstraction: the source-facing lemma should be stated directly using the chapter owner
  `associatedModuleSheaf` with its source-facing notations `𝓕[α]_M` and `𝓕_ M`, the ringed-space
  inverse-image owner `g^*`, and the module-side change of rings owner `ModuleCat.extendScalars`,
  rather than a local tensor-product wrapper for the base-changed module;
- primitive data: a morphism of ringed spaces `g : Y ⟶ X` and a
  `Γ(X, \mathcal O_X)`-module `M`;
- derived API: the pullback comparison identifying `g^*` of the associated sheaf on `X` with the
  associated sheaf on `Y` attached to the extended module over `Γ(Y, \mathcal O_Y)`.

Source/core/bridge triage:
- `source-facing`: the pullback/base-change comparison for associated module sheaves;
- `core/canonical`: `associatedModuleSheaf`, `RingedSpace.Hom.pullback`, and
  `ModuleCat.extendScalars`;
- `bridge/view`: the global-sections ring map `((SheafedSpace.Γ.map g.op).hom)` and the
  owner comparison `SheafOfModules.pullbackComp` used in the proof route.
-/

-- Proof sketch: specialize the canonical pullback-composition isomorphism
-- `SheafOfModules.pullbackComp` to the owner construction from Lemma `17.10.5`, then simplify the
-- resulting composite pullback to the associated sheaf on `Y` attached to the extended module.
/-- Lemma 17.10.7: after pullback along `g : Y ⟶ X`, the pullback of the associated module sheaf
is canonically isomorphic to the associated sheaf on `Y`
attached to `Γ(Y, \mathcal O_Y) \otimes_{Γ(X, \mathcal O_X)} M`. -/
noncomputable abbrev pullback_associated_globalSectionsModule
    {X Y : RingedSpace.{u}} (g : Y ⟶ X)
    (M : ModuleCat (X.presheaf.obj (op ⊤))) :
    ((g^*).obj (𝓕_ M)) ≅
      𝓕_ ((ModuleCat.extendScalars ((SheafedSpace.Γ.map g.op).hom)).obj M) := by
  refine (SheafOfModules.pullbackComp _ _).app _ ≪≫ ?_
  -- This remaining comparison is the singleton-source change-of-rings identification.
  sorry

end AlgebraicGeometry
