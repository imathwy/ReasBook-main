import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_10_6

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
/-- Helper for Lemma 17.10.7: the pullback of `𝓕_M` along `g` first rewrites, via
`SheafOfModules.pullbackComp`, to the associated sheaf on `Y` built from the composite map on
global sections. -/
private noncomputable abbrev pullbackAssociatedModuleSheaf_compIso
    {X Y : RingedSpace.{u}} (g : Y ⟶ X)
    (M : ModuleCat (X.presheaf.obj (op ⊤))) :
    ((RingedSpace.Hom.pullback g).obj (𝓕_ M)) ≅
      𝓕[((SheafedSpace.Γ.map g.op).hom)]_M := by
  -- Proof comment: this is exactly the pseudofunctorial pullback comparison for the singleton
  -- source morphism defining `𝓕_ M`.
  exact (SheafOfModules.pullbackComp _ _).app _

/-- Helper for Lemma 17.10.7: on each open of `Y`, the presheaf underlying `𝓕[α]_M` computes the
same module as first extending scalars from `R` to `Γ(Y, \mathcal O_Y)` and then restricting from
global sections to that open. -/
private theorem associatedModulePresheafObjExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) (U : (Opens Y)ᵒᵖ) :
    (associatedModulePresheaf α M).obj U ≅
      (associatedModulePresheaf (RingHom.id _) ((ModuleCat.extendScalars α).obj M)).obj U := by
  let iU : op (⊤ : Opens Y) ⟶ U :=
    (homOfLE (show unop U ≤ (⊤ : Opens Y) from by
      intro x hx
      trivial)).op
  let βU : Y.presheaf.obj (op ⊤) →+* Y.presheaf.obj U :=
    (Y.presheaf.map iU).hom
  -- Proof comment: after unfolding the singleton-source pullback model on `U`, both sides become
  -- the two standard iterated scalar extensions from `R` to `\mathcal O_Y(U)`.
  simpa [associatedModulePresheaf, iU, βU] using
    ((ModuleCat.extendScalarsComp α βU).app M)

/-- Helper for Lemma 17.10.7: the public presheaf model of the associated sheaf is compatible
with extending scalars along the global-sections map `α`. -/
private theorem associatedModulePresheafExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    associatedModulePresheaf α M ≅
      associatedModulePresheaf (RingHom.id _) ((ModuleCat.extendScalars α).obj M) := by
  -- TODO: package the objectwise comparison from
  -- `associatedModulePresheafObjExtendScalarsIso` into a `NatIso`, then check naturality against
  -- the restriction maps of `associatedModulePresheaf`.
  sorry

/-- Helper for Lemma 17.10.7: the associated sheaf for a ring map `α` is canonically the same as
the identity-associated sheaf of the extended module over `Γ(Y, \mathcal O_Y)`. -/
private theorem associatedModuleSheafExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    𝓕[α]_M ≅ 𝓕_ ((ModuleCat.extendScalars α).obj M) := by
  -- TODO: transport `associatedModulePresheafExtendScalarsIso` across the two
  -- `associatedModuleSheafFromPresheafIso` isomorphisms.
  sorry

/-- Lemma 17.10.7: after pullback along `g : Y ⟶ X`, the pullback of the associated module sheaf
is canonically isomorphic to the associated sheaf on `Y`
attached to `Γ(Y, \mathcal O_Y) \otimes_{Γ(X, \mathcal O_X)} M`. -/
noncomputable abbrev pullback_associated_globalSectionsModule
    {X Y : RingedSpace.{u}} (g : Y ⟶ X)
    (M : ModuleCat (X.presheaf.obj (op ⊤))) :
    ((RingedSpace.Hom.pullback g).obj (𝓕_ M)) ≅
      𝓕_ ((ModuleCat.extendScalars ((SheafedSpace.Γ.map g.op).hom)).obj M) := by
  -- Route correction: `((g^*).obj ...)` does not parse reliably in this file, so keep the
  -- same pullback owner with the explicit `RingedSpace.Hom.pullback g` spelling.
  refine pullbackAssociatedModuleSheaf_compIso g M ≪≫ ?_
  -- Proof comment: the remaining comparison is the base-change identification for the associated
  -- sheaf itself, now isolated in the dedicated helper above.
  exact associatedModuleSheafExtendScalarsIso ((SheafedSpace.Γ.map g.op).hom) M

end AlgebraicGeometry
