import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap17.Definition_17_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 17.10.7: the singleton top open in `(Opens X)ᵒᵖ` is initial. -/
private abbrev topOpensIsInitial (X : RingedSpace.{u}) : Limits.IsInitial (op (⊤ : Opens X)) :=
  Limits.IsInitial.ofUniqueHom
    (fun U : (Opens X)ᵒᵖ ↦
      (homOfLE (show unop U ≤ (⊤ : Opens X) from by
        intro x hx
        trivial)).op)
    (fun U f ↦ Subsingleton.elim _ _)

/-- Helper for Lemma 17.10.7: the singleton source topological space used to model an
`R`-module sheaf over a point. -/
private abbrev globalSectionsSourceSpace : TopCat := TopCat.of PUnit

/-- Helper for Lemma 17.10.7: the unique point of the singleton source space. -/
private abbrev globalSectionsSourcePoint : globalSectionsSourceSpace := PUnit.unit

/-- Helper for Lemma 17.10.7: any open containing the singleton point is the top open. -/
private theorem globalSectionsSourceOpen_eq_top {U : Opens globalSectionsSourceSpace}
    (h : PUnit.unit ∈ U) :
    U = ⊤ := by
  ext y
  cases y
  simp [h]

/-- Helper for Lemma 17.10.7: any open omitting the singleton point is the bottom open. -/
private theorem globalSectionsSourceOpen_eq_bot {U : Opens globalSectionsSourceSpace}
    (h : PUnit.unit ∉ U) :
    U = ⊥ := by
  ext y
  cases y
  constructor
  · intro hy
    exact (h hy).elim
  · intro hy
    exact False.elim hy

/-- Helper for Lemma 17.10.7: the singleton ringed space with structure sheaf constantly `R`
on its unique nonempty open. -/
private noncomputable def globalSectionsSourceRingedSpace (R : Type u) [CommRing R] : RingedSpace :=
  let pointSheaf := skyscraperSheaf PUnit.unit (CommRingCat.of R)
  { carrier := globalSectionsSourceSpace
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

/-- Helper for Lemma 17.10.7: the sheaf of coefficient rings on the singleton source. -/
private noncomputable abbrev globalSectionsSourceRingCatSheaf (R : Type u) [CommRing R] :=
  RingedSpace.ringCatSheaf (globalSectionsSourceRingedSpace R)

/-- Helper for Lemma 17.10.7: the top-open ring on the singleton source is exactly `R`. -/
private theorem globalSectionsSourceRingCatSheaf_obj_top (R : Type u) [CommRing R] :
    (globalSectionsSourceRingCatSheaf R).obj.obj (op (⊤ : Opens globalSectionsSourceSpace)) =
      RingCat.of R := by
  let pointSheaf : Sheaf CommRingCat globalSectionsSourceSpace :=
    skyscraperSheaf PUnit.unit (CommRingCat.of R)
  change
    (forget₂ CommRingCat RingCat).obj
        (pointSheaf.obj.obj (op ⊤)) =
      RingCat.of R
  simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf]
  rfl

/-- Helper for Lemma 17.10.7: the singleton-source presheaf of modules attached to `M`. -/
private noncomputable def globalSectionsSourceModulePresheafObj
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    (U : (Opens globalSectionsSourceSpace)ᵒᵖ) →
      ModuleCat ((globalSectionsSourceRingCatSheaf R).obj.obj U) :=
  fun U ↦ by
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
      subst hU'
      exact
        (ModuleCat.restrictScalars
          (eqToHom (globalSectionsSourceRingCatSheaf_obj_top R)).hom).obj M
    · exact
        ⊤_ ModuleCat ((globalSectionsSourceRingCatSheaf R).obj.obj U)

/-- Helper for Lemma 17.10.7: on the top open, the singleton-source module presheaf is the
restricted `R`-module `M`. -/
private theorem globalSectionsSourceModulePresheafObj_op_top
    (R : Type u) [CommRing R] (M : ModuleCat R) :
    globalSectionsSourceModulePresheafObj R M (op (⊤ : Opens globalSectionsSourceSpace)) =
      (ModuleCat.restrictScalars
        (eqToHom (globalSectionsSourceRingCatSheaf_obj_top R)).hom).obj M := by
  simp [globalSectionsSourceModulePresheafObj]

/-- Helper for Lemma 17.10.7: on the bottom open, the singleton-source module presheaf is the
terminal module. -/
private theorem globalSectionsSourceModulePresheafObj_op_bot
    (R : Type u) [CommRing R] (M : ModuleCat R) :
    globalSectionsSourceModulePresheafObj R M (op (⊥ : Opens globalSectionsSourceSpace)) =
      ⊤_ ModuleCat ((globalSectionsSourceRingCatSheaf R).obj.obj
        (op (⊥ : Opens globalSectionsSourceSpace))) := by
  dsimp [globalSectionsSourceModulePresheafObj]
  split_ifs with h
  · exact (by simpa using h : False).elim
  · rfl

/-- Helper for Lemma 17.10.7: the singleton-source restriction map is the explicit top-branch
restriction-of-scalars map, and otherwise the zero map into the terminal bottom value. -/
private noncomputable def globalSectionsSourceModulePresheafMap
    (R : Type u) [CommRing R]
    (M : ModuleCat R)
    {U V : (Opens globalSectionsSourceSpace)ᵒᵖ} (i : U ⟶ V) :
    globalSectionsSourceModulePresheafObj R M U ⟶
      (ModuleCat.restrictScalars ((globalSectionsSourceRingCatSheaf R).obj.map i).hom).obj
        (globalSectionsSourceModulePresheafObj R M V) := by
  by_cases hV : PUnit.unit ∈ unop V
  · have hU : PUnit.unit ∈ unop U := i.unop.le hV
    have hU' : U = op ⊤ := by
      simpa using congrArg op (globalSectionsSourceOpen_eq_top hU)
    have hV' : V = op ⊤ := by
      simpa using congrArg op (globalSectionsSourceOpen_eq_top hV)
    subst hU'
    subst hV'
    have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
    exact
      (ModuleCat.restrictScalarsId'
        ((globalSectionsSourceRingCatSheaf R).obj.map i).hom
        (by
          subst hi
          exact congrArg RingCat.Hom.hom
            ((globalSectionsSourceRingCatSheaf R).obj.map_id (op ⊤)))).inv.app
        (globalSectionsSourceModulePresheafObj R M (op ⊤))
  · simpa [globalSectionsSourceModulePresheafObj, hV] using
      (0 :
        globalSectionsSourceModulePresheafObj R M U ⟶
          (ModuleCat.restrictScalars
            ((globalSectionsSourceRingCatSheaf R).obj.map i).hom).obj
              (globalSectionsSourceModulePresheafObj R M V))

/-- Helper for Lemma 17.10.7: on the top open, the singleton-source restriction map is the
explicit identity restriction-of-scalars isomorphism. -/
private theorem globalSectionsSourceModulePresheafMap_op_top
    (R : Type u) [CommRing R] (M : ModuleCat R)
    (i : op (⊤ : Opens globalSectionsSourceSpace) ⟶ op ⊤) :
    globalSectionsSourceModulePresheafMap R M i =
      (ModuleCat.restrictScalarsId'
        ((globalSectionsSourceRingCatSheaf R).obj.map i).hom
        (by
          have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
          subst hi
          exact congrArg RingCat.Hom.hom
            ((globalSectionsSourceRingCatSheaf R).obj.map_id (op ⊤)))).inv.app
        (globalSectionsSourceModulePresheafObj R M (op ⊤)) := sorry

/-- Helper for Lemma 17.10.7: restricting scalars preserves the terminal bottom-open value. -/
private noncomputable def
    globalSectionsSourceModulePresheaf_restrictScalars_obj_op_bot_isTerminal
    (R : Type u) [CommRing R] (M : ModuleCat R)
    {U : (Opens globalSectionsSourceSpace)ᵒᵖ}
    (i : U ⟶ op (⊥ : Opens globalSectionsSourceSpace)) :
    IsTerminal
      ((ModuleCat.restrictScalars
          (RingCat.Hom.hom ((globalSectionsSourceRingCatSheaf R).obj.map i))).obj
        (globalSectionsSourceModulePresheafObj R M (op (⊥ : Opens globalSectionsSourceSpace)))) := by
  let F := ModuleCat.restrictScalars
    (RingCat.Hom.hom ((globalSectionsSourceRingCatSheaf R).obj.map i))
  have hterminalTop :
      IsTerminal
        (F.obj
          (⊤_ ModuleCat ↑((globalSectionsSourceRingCatSheaf R).obj.obj
            (op (⊥ : Opens globalSectionsSourceSpace))))) := by
    exact
      IsTerminal.ofIso
        (terminalIsTerminal :
          IsTerminal
            (⊤_ ModuleCat ↑((globalSectionsSourceRingCatSheaf R).obj.obj U)))
        (PreservesTerminal.iso F).symm
  exact
    IsTerminal.ofIso hterminalTop
      (Functor.mapIso F (eqToIso (globalSectionsSourceModulePresheafObj_op_bot R M))).symm

/-- Helper for Lemma 17.10.7: every singleton-source restriction map landing in the bottom open
is zero. -/
private theorem globalSectionsSourceModulePresheafMap_to_op_bot
    (R : Type u) [CommRing R] (M : ModuleCat R)
    {U : (Opens globalSectionsSourceSpace)ᵒᵖ}
    (i : U ⟶ op (⊥ : Opens globalSectionsSourceSpace)) :
    globalSectionsSourceModulePresheafMap R M i = 0 := by
  dsimp [globalSectionsSourceModulePresheafMap]
  split_ifs with hV hU
  · exact (by simpa using hV : False).elim
  · exact
      (globalSectionsSourceModulePresheaf_restrictScalars_obj_op_bot_isTerminal R M i).hom_ext _ _
  · exact
      (globalSectionsSourceModulePresheaf_restrictScalars_obj_op_bot_isTerminal R M i).hom_ext _ _

/-- Helper for Lemma 17.10.7: when all opens are the top open, the composition law is the
standard composition law for restriction of scalars. -/
private theorem globalSectionsSourceModulePresheafMap_comp_op_top
    (R : Type u) [CommRing R] (M : ModuleCat R)
    (i j : op (⊤ : Opens globalSectionsSourceSpace) ⟶ op ⊤) :
    globalSectionsSourceModulePresheafMap R M (i ≫ j) =
      globalSectionsSourceModulePresheafMap R M i ≫
        (ModuleCat.restrictScalars ((globalSectionsSourceRingCatSheaf R).obj.map i).hom).map
          (globalSectionsSourceModulePresheafMap R M j) ≫
        (ModuleCat.restrictScalarsComp'
            ((globalSectionsSourceRingCatSheaf R).obj.map i).hom
            ((globalSectionsSourceRingCatSheaf R).obj.map j).hom
            ((globalSectionsSourceRingCatSheaf R).obj.map (i ≫ j)).hom
            (congrArg RingCat.Hom.hom
              ((globalSectionsSourceRingCatSheaf R).obj.map_comp i j))).inv.app
          (globalSectionsSourceModulePresheafObj R M (op (⊤ : Opens globalSectionsSourceSpace))) := by
  -- Route correction: once the one-point space is normalized to `⊤`, both arrows are identities,
  -- so only the explicit restriction-of-scalars coherence remains.
  have hi : i = 𝟙 (op (⊤ : Opens globalSectionsSourceSpace)) := Subsingleton.elim _ _
  have hj : j = 𝟙 (op (⊤ : Opens globalSectionsSourceSpace)) := Subsingleton.elim _ _
  subst hi
  subst hj
  rw [globalSectionsSourceModulePresheafMap_op_top, globalSectionsSourceModulePresheafMap_op_top]
  ext m
  convert (rfl : m = m) using 1 <;> simp

/-- Helper for Lemma 17.10.7: the singleton-source presheaf keeps `M` on the top open and the
terminal module on the empty open. -/
private noncomputable def globalSectionsSourceModulePresheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    PresheafOfModules (globalSectionsSourceRingCatSheaf R).obj := sorry

/-- Helper for Lemma 17.10.7: the bottom-open value of the underlying additive presheaf is
terminal. -/
private noncomputable def globalSectionsSourceModulePresheaf_presheaf_obj_bot_isTerminal
    (R : Type u) [CommRing R] (M : ModuleCat R) :
    IsTerminal (((globalSectionsSourceModulePresheaf R M).presheaf).obj
      (op (⊥ : Opens globalSectionsSourceSpace))) := sorry

/-- Helper for Lemma 17.10.7: package the singleton-source module presheaf as a sheaf of
modules. -/
private noncomputable def globalSectionsSourceModuleSheaf
    (R : Type u) [CommRing R]
    (M : ModuleCat R) :
    SheafOfModules (globalSectionsSourceRingCatSheaf R) where
  val := globalSectionsSourceModulePresheaf R M
  isSheaf := by
    -- Proof comment: on the one-point space, sheafiness reduces to terminality on the empty open.
    exact TopCat.Presheaf.isSheaf_on_punit_of_isTerminal _
      (globalSectionsSourceModulePresheaf_presheaf_obj_bot_isTerminal R M)

/-- Helper for Lemma 17.10.7: a linear map of `R`-modules induces a morphism of the
corresponding singleton-source sheaves. -/
private noncomputable def globalSectionsSourceModuleSheafMap
    (R : Type u) [CommRing R]
    {M N : ModuleCat R} (f : M ⟶ N) :
    globalSectionsSourceModuleSheaf R M ⟶ globalSectionsSourceModuleSheaf R N := sorry

/-- Helper for Lemma 17.10.7: the singleton-source construction is functorial in the module. -/
private noncomputable def globalSectionsSourceModuleFunctor
    (R : Type u) [CommRing R] :
    ModuleCat R ⥤ SheafOfModules (globalSectionsSourceRingCatSheaf R) := sorry

/-- Helper for Lemma 17.10.7: the structural sheaf map `π^#` on the singleton source induced by
`α : R → Γ(X, \mathcal O_X)`. -/
private noncomputable def globalSectionsSourceSheafMap
    {X : RingedSpace.{u}}
    (R : Type u) [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    (globalSectionsSourceRingedSpace R).presheaf ⟶
      (ofHom (ContinuousMap.const X PUnit.unit)) _* X.presheaf := sorry

/-- Helper for Lemma 17.10.7: the map `π : X ⟶ (*, R)` corresponding to
`α : R → Γ(X, \mathcal O_X)`. -/
private noncomputable def globalSectionsSourceMorphism
    {X : RingedSpace.{u}}
    (R : Type u) [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ globalSectionsSourceRingedSpace R :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const X PUnit.unit)
      c := globalSectionsSourceSheafMap R α }

/-- Helper for Lemma 17.10.7: the owner functor sending an `R`-module to the associated
`\mathcal O_X`-module via pullback from the singleton source. -/
private noncomputable def globalSectionsModuleFunctor
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) :
    ModuleCat R ⥤ SheafOfModules ((RingedSpace.ringCatSheaf X)) :=
  globalSectionsSourceModuleFunctor R ⋙ RingedSpace.Hom.pullback (globalSectionsSourceMorphism R α)

/-- Helper for Lemma 17.10.7: the associated `\mathcal O_X`-module attached to the `R`-module
`M` through `α`. -/
private abbrev associatedModuleSheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  (globalSectionsModuleFunctor α).obj M

/-- Helper for Lemma 17.10.7: the presheaf model `U ↦ \mathcal O_X(U) \otimes_R M` of the
associated sheaf. -/
private abbrev associatedModulePresheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    PresheafOfModules (RingedSpace.ringCatSheaf X).obj :=
  ((SheafOfModules.forget (globalSectionsSourceRingCatSheaf R)) ⋙
      PresheafOfModules.pullback
        (RingedSpace.Hom.toRingCatSheafHom (globalSectionsSourceMorphism R α)).hom).obj
    (globalSectionsSourceModuleSheaf R M)

/-- Helper for Lemma 17.10.7: the sheafification of the associated presheaf model. -/
private abbrev associatedModuleSheafFromPresheaf
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    RingedSpace.Modules X :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
    (associatedModulePresheaf α M)

/-- Helper for Lemma 17.10.7: the owner sheaf is the sheafification of its presheaf model. -/
private noncomputable abbrev associatedModuleSheafFromPresheafIso
    {X : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    associatedModuleSheaf α M ≅ associatedModuleSheafFromPresheaf α M := sorry

/- Source-facing notation localized here to avoid the broken `Definition_17_10_6` import. -/
scoped notation:max "𝓕[" α "]_" M:max => associatedModuleSheaf α M
scoped notation:max "𝓕_" M:max => associatedModuleSheaf (RingHom.id _) M

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
      𝓕[((SheafedSpace.Γ.map g.op).hom)]_M := sorry

/-- Helper for Lemma 17.10.7: on each open of `Y`, the presheaf underlying `𝓕[α]_M` computes the
same module as first extending scalars from `R` to `Γ(Y, \mathcal O_Y)` and then restricting from
global sections to that open. -/
private noncomputable abbrev associatedModulePresheafObjExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) (U : (Opens Y)ᵒᵖ) :
    (associatedModulePresheaf α M).obj U ≅
      (associatedModulePresheaf (RingHom.id _) ((ModuleCat.extendScalars α).obj M)).obj U := sorry

/-- Helper for Lemma 17.10.7: the public presheaf model of the associated sheaf is compatible
with extending scalars along the global-sections map `α`. -/
private noncomputable abbrev associatedModulePresheafExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    associatedModulePresheaf α M ≅
      associatedModulePresheaf (RingHom.id _) ((ModuleCat.extendScalars α).obj M) := sorry

/-- Helper for Lemma 17.10.7: the associated sheaf for a ring map `α` is canonically the same as
the identity-associated sheaf of the extended module over `Γ(Y, \mathcal O_Y)`. -/
private noncomputable abbrev associatedModuleSheafExtendScalarsIso
    {Y : RingedSpace.{u}} {R : Type u} [CommRing R]
    (α : R →+* Y.presheaf.obj (op ⊤)) (M : ModuleCat R) :
    𝓕[α]_M ≅ 𝓕_ ((ModuleCat.extendScalars α).obj M) := sorry

/-- Lemma 17.10.7: after pullback along `g : Y ⟶ X`, the pullback of the associated module sheaf
is canonically isomorphic to the associated sheaf on `Y`
attached to `Γ(Y, \mathcal O_Y) \otimes_{Γ(X, \mathcal O_X)} M`. -/
@[stacks 01BJ]
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
