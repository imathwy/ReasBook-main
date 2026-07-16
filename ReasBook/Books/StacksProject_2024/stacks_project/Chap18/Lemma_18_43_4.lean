import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open PresheafOfModules

noncomputable section

universe u v w z

namespace CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- Helper for Lemma 18.43.4: local fallback owner for the Chapter 18 local-Hom sheaf while the
earlier chapter owner file remains broken. This keeps the target file self-contained enough to
expose its remaining proof frontier. -/
def localHomSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (ℱ : PresheafOfModules ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪).obj)
    (𝒢 : SheafOfModules ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪)) :
    SheafOfModules ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj 𝒪) := by
  -- TODO: rebuild the chapter-owner local Hom sheaf here by sheafifying the pointwise presheaf of
  -- module morphisms over the ambient ring sheaf; the current file only needs the source-facing
  -- comparison layer, but `lake lean` cannot use the earlier owner file while it is broken.
  sorry

end PresheafOfModules

namespace Sheaf

section ConstantModuleBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [Ring Λ]
variable [HasWeakSheafify J RingCat.{max u v}]
variable [J.WEqualsLocallyBijective RingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Helper for Lemma 18.43.4: the underlying presheaf of `Λ`-modules of a `ModuleCat`-valued sheaf
viewed as a presheaf of modules over the constant `RingCat`-valued presheaf with value `Λ`. -/
private abbrev toConstantModulePresheaf (F : Sheaf J (ModuleCat.{max u v} Λ)) :
    PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    F.1 ⋙ forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v}
  letI (X : Cᵒᵖ) : Module ↑(((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).obj X) ↑(P.obj X) := by
    change Module Λ ↑(F.1.obj X)
    infer_instance
  PresheafOfModules.ofPresheaf P
    (fun {X Y} f r m ↦ by
      -- Proof comment: the restriction maps of `F` are `Λ`-linear, so they commute with scalar
      -- multiplication over the constant ring presheaf.
      change ((F.1.map f).hom) (r • m) = (RingHom.id Λ) r • ((F.1.map f).hom m)
      exact (F.1.map f).hom.map_smul r m)

/-- Helper for Lemma 18.43.4: the canonical bridge viewing a sheaf of `Λ`-modules as a sheaf of
modules over the constant ring sheaf `\underline{\Lambda}`. -/
noncomputable abbrev toConstantModuleSheaf (F : Sheaf J (ModuleCat.{max u v} Λ)) :
    SheafOfModules ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) :=
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  letI : Presheaf.IsLocallyInjective J α := (J.W_toSheafify _).isLocallyInjective
  letI : Presheaf.IsLocallySurjective J α := (J.W_toSheafify _).isLocallySurjective
  -- Proof comment: sheafify the underlying presheaf of modules along the canonical comparison
  -- from the constant ring presheaf to the constant ring sheaf.
  (PresheafOfModules.sheafification α).obj (toConstantModulePresheaf F)

end ConstantModuleBridge

section FinitePresentationBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [Ring Λ]
variable [HasWeakSheafify J RingCat.{max u v}]
variable [J.WEqualsLocallyBijective RingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-- Helper for Lemma 18.43.4: source-facing finite presentation for a sheaf of `Λ`-modules,
obtained by transporting the canonical owner predicate across `toConstantModuleSheaf`. -/
abbrev IsFinitePresentation (F : Sheaf J (ModuleCat.{max u v} Λ)) : Prop :=
  F.toConstantModuleSheaf.IsFinitePresentation

end FinitePresentationBridge

end Sheaf

/- Domain-style sampling for Lemma 18.43.4:
- primary domain: locally constant sheaves of `\Lambda`-modules on a site, their local Hom, and
  the associated local isomorphism sheaf;
- sampled owner declarations:
  `Sheaf.over`,
  `PresheafOfModules.localHomSheaf`,
  `CategoryTheory.Sheaf.toConstantModuleSheaf`,
  `constantCommuteCompose`,
  `CategoryTheory.Sheaf.IsFinitePresentation`,
  `Sheaf.IsLocallyConstant`,
  `constantSheaf`;
- best owner abstraction: the chapter owner `PresheafOfModules.localHomSheaf`, specialized to the
  constant commutative ring sheaf `((constantSheaf J CommRingCat).obj (CommRingCat.of Λ))`; the
  source-facing fixed-ring local-Hom object `ℋom[Λ](F, G)` should therefore be treated only as a
  notation-level surface over the bridge/view `sheafHomModule`, tied back to that owner through a
  public comparison theorem after passing the inputs through `Sheaf.toConstantModuleSheaf`, while
  slice restriction remains expressed through the canonical owner `Sheaf.over`;
- primitive data: the site `(C, J)`, the ring `\Lambda`, the source-facing finite-presentation
  owner `F.IsFinitePresentation`, and the canonical restriction-of-scalars comparison from the
  forgotten constant commutative ring sheaf to the constant `RingCat`-valued sheaf;
- derived API: the source-facing notation `ℋom[Λ](F, G)`, the underlying bridge
  `sheafHomModule`, its public comparison with the specialized canonical owner
  `PresheafOfModules.localHomSheaf`, and the companion
  isomorphism-sheaf statements.

Source/core/bridge triage:
- `source-facing`: `sheafIso` and the four Stacks-style constancy and local-constancy theorems
  below;
- `core/canonical`: `PresheafOfModules.localHomSheaf` and
  `CategoryTheory.Sheaf.IsFinitePresentation`;
- `bridge/view`: `CategoryTheory.Sheaf.toConstantModuleSheaf`, the canonical restriction of
  scalars along `constantCommuteCompose`, the bridge definition `sheafHomModule` underlying the
  notation `ℋom[Λ](F, G)`, its comparison theorem to the specialized canonical owner
  `PresheafOfModules.localHomSheaf`, and the `Type`-valued local isomorphism sheaf `sheafIso`. -/

section HomSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [CommRing Λ]

/-- Helper for Lemma 18.43.4: relocalizing an object of a slice site along the identity map does
not change that slice object. -/
private theorem over_map_id_obj_eq
    (U : Cᵒᵖ) (X : Over U.unop) :
    ((Over.map (𝟙 U.unop)).obj X) = X := by
  -- Reduce identity relocalization to the identity functor and evaluate at `X`.
  simpa using congrArg (fun F ↦ F.obj X) (Over.mapId_eq U.unop)

/-- Helper for Lemma 18.43.4: relocalizing in two steps agrees with relocalizing along the
composite map. -/
private theorem over_map_comp_obj_eq
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (X : Over W.unop) :
    ((Over.map (g.unop ≫ f.unop)).obj X) =
      ((Over.map f.unop).obj ((Over.map g.unop).obj X)) := by
  -- Reduce the composite relocalization functor to a composite of relocalizations.
  simpa using congrArg (fun F ↦ F.obj X) (Over.mapComp_eq g.unop f.unop)

/-- Helper for Lemma 18.43.4: after evaluating at a local section, restricting a local morphism
along `f` amounts to relocalizing the slice object index. -/
private theorem sheafHomModulePresheaf_map_app
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over Y.unop)ᵒᵖ) :
    (((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ).hom.app U) =
      φ.hom.app (op ((Over.map f.unop).obj U.unop)) := by
  -- `overMapPullback` acts on natural transformations by relocalizing the slice-object index.
  rfl

/-- Helper for Lemma 18.43.4: after evaluating at a local section, restricting a local morphism
along `f` amounts to relocalizing the slice object index. -/
private theorem sheafHomModulePresheaf_map_app_apply
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over Y.unop)ᵒᵖ)
    (u : ↑(((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).obj (F.over X.unop)).obj.obj U)) :
    (ModuleCat.Hom.hom (((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ).hom.app U)) u =
      (ModuleCat.Hom.hom (φ.hom.app (op ((Over.map f.unop).obj U.unop)))) u := by
  -- `overMapPullback` acts on natural transformations by relocalizing the slice-object index.
  rfl

/-- Helper for Lemma 18.43.4: after evaluating at a local section, restricting a scalar multiple
of a local morphism agrees with scaling the restricted value. -/
private theorem overMapPullback_map_smul_app_apply
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : Λ)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over Y.unop)ᵒᵖ)
    (u : ↑(((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).obj (F.over X.unop)).obj.obj U)) :
    (ModuleCat.Hom.hom (((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map
      (r • φ)).hom.app U)) u =
      r • (ModuleCat.Hom.hom (((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map
        φ).hom.app U)) u := by
  -- Restriction is computed componentwise on the localized natural transformation.
  rfl

/-- Helper for Lemma 18.43.4: transporting evaluation of a local morphism along an equality of
slice objects is definitionally trivial after reducing to the reflexive case. -/
private theorem sheaf_over_hom_app_transport
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {U : C}
    (φ : F.over U ⟶ G.over U) {X Y : (Over U)ᵒᵖ} (h : X = Y) :
    Eq.ndrec (motive := fun Z ↦ (F.over U).obj.obj Z ⟶ (G.over U).obj.obj Z)
      (φ.hom.app X) h = φ.hom.app Y := by
  -- The component transport disappears after reducing to the reflexive equality case.
  cases h
  rfl

/-- Helper for Lemma 18.43.4: transporting evaluation of a local morphism along an equality of
slice objects is definitionally trivial after reducing to the reflexive case. -/
private theorem sheaf_over_hom_app_transport_apply
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {U : C}
    (φ : F.over U ⟶ G.over U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (F.over U).obj.obj X) :
    h ▸ ModuleCat.Hom.hom (φ.hom.app X) x =
      ModuleCat.Hom.hom (φ.hom.app Y) (h ▸ x) := by
  -- The transport only changes the slice-object index.
  cases h
  rfl

/-- Helper for Lemma 18.43.4: the exact evaluation-level transport left after rewriting a
restricted local morphism is definitionally trivial once the slice-object equality is reflexive. -/
private theorem sheaf_over_hom_app_eval_transport_ndrec
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {U : C}
    (φ : F.over U ⟶ G.over U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (F.over U).obj.obj Y) :
    Eq.ndrec
        (motive := fun Z ↦ (G.over U).obj.obj Z)
        (ModuleCat.Hom.hom (φ.hom.app X) (h.symm ▸ x)) h =
      ModuleCat.Hom.hom (φ.hom.app Y) x := by
  -- The dependent transport disappears after reducing to the reflexive equality case.
  cases h
  rfl

/-- Helper for Lemma 18.43.4: if two slice-object indices agree, evaluating on the first index
with the input transported back to it matches evaluation on the second index up to the induced
transport on the target section. -/
private theorem sheaf_over_hom_app_eq_of_section_transport
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {U : C}
    (φ : F.over U ⟶ G.over U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (F.over U).obj.obj Y) :
    ModuleCat.Hom.hom (φ.hom.app X) (h.symm ▸ x) =
      h.symm ▸ ModuleCat.Hom.hom (φ.hom.app Y) x := by
  -- Once the slice-object equality is reflexive, both sides become the same evaluation term.
  cases h
  rfl

/-- Helper for Lemma 18.43.4: transporting dependent data along an equality and back is trivial. -/
private theorem localized_section_double_transport_eq
    {ι : Sort _} (P : ι → Sort _) {X Y : ι} (h : X = Y) (u : P Y) :
    Eq.ndrec (motive := P) (Eq.ndrec (motive := P) u h.symm) h = u := by
  -- Double transport along an equality collapses after reducing to the reflexive case.
  cases h
  rfl

/-- Helper for Lemma 18.43.4: restriction along the identity map acts trivially on local
`\Lambda`-linear morphisms. -/
private theorem sheafHomModuleRestrictIdAppEq
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) (X : Cᵒᵖ)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over X.unop)ᵒᵖ) :
    (((J.overMapPullback (ModuleCat.{max u v} Λ) (𝟙 X.unop)).map φ).hom.app U) =
      φ.hom.app U := by
  -- Route correction: normalize the identity restriction to the relocalized slice object, then
  -- reduce the relocalized slice object to the original one by the identity-map equality.
  change φ.hom.app (op ((Over.map (𝟙 X.unop)).obj U.unop)) = φ.hom.app U
  cases congrArg op (over_map_id_obj_eq X U.unop)
  rfl

/-- Helper for Lemma 18.43.4: restriction along a composite map produces the same localized
component as two successive restrictions. -/
private theorem sheafHomModuleRestrictCompAppEq
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : F.over X.unop ⟶ G.over X.unop) (U : (Over Z.unop)ᵒᵖ) :
    (((J.overMapPullback (ModuleCat.{max u v} Λ) ((f ≫ g).unop)).map φ).hom.app U) =
      (((J.overMapPullback (ModuleCat.{max u v} Λ) g.unop).map
        ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ)).hom.app U) := by
  -- Route correction: rewrite both restrictions to evaluations at their relocalized slice
  -- objects, then use the slice-level composite normalization to compare the indices.
  change φ.hom.app (op ((Over.map ((f ≫ g).unop)).obj U.unop)) =
    (((J.overMapPullback (ModuleCat.{max u v} Λ) g.unop).map
      ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ)).hom.app U)
  change φ.hom.app (op ((Over.map ((f ≫ g).unop)).obj U.unop)) =
    (((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ).hom.app
      (op ((Over.map g.unop).obj U.unop)))
  change φ.hom.app (op ((Over.map ((f ≫ g).unop)).obj U.unop)) =
    φ.hom.app (op ((Over.map f.unop).obj ((Over.map g.unop).obj U.unop)))
  cases congrArg op (over_map_comp_obj_eq f g U.unop)
  rfl

/-- Helper for Lemma 18.43.4: restriction along the identity map acts trivially on local
`\Lambda`-linear morphisms. -/
private theorem sheafHomModule_restrict_id
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) (X : Cᵒᵖ)
    (φ : F.over X.unop ⟶ G.over X.unop) :
    (J.overMapPullback (ModuleCat.{max u v} Λ) (𝟙 X.unop)).map φ = φ := by
  -- Evaluate both natural transformations at each slice object and compare the normalized
  -- components.
  ext U u
  rw [sheafHomModuleRestrictIdAppEq]

/-- Helper for Lemma 18.43.4: restriction along a composite map agrees with successive
restriction on local `\Lambda`-linear morphisms. -/
private theorem sheafHomModule_restrict_comp
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : F.over X.unop ⟶ G.over X.unop) :
    (J.overMapPullback (ModuleCat.{max u v} Λ) ((f ≫ g).unop)).map φ =
      (J.overMapPullback (ModuleCat.{max u v} Λ) g.unop).map
        ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ) := by
  -- Evaluate both natural transformations at each slice object and compare the normalized
  -- components.
  ext U u
  rw [sheafHomModuleRestrictCompAppEq]

/-- The source-facing fixed-ring local-Hom presheaf between two sheaves of `\Lambda`-modules on a
site. Its value on `U` is the `\Lambda`-module of morphisms between the restrictions of `F` and
  `G` to the slice site above `U`. This is the source-facing fixed-ring view of the canonical
  Chapter 18 local-Hom owner. -/
private def sheafHomModulePresheaf
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) : Cᵒᵖ ⥤ ModuleCat.{max u v} Λ where
  obj X := by
    let U := X.unop
    exact ModuleCat.of Λ (F.over U ⟶ G.over U)
  map {X Y} f := ModuleCat.ofHom
    { toFun := fun φ ↦
        (J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ
      map_add' := by
        -- Restriction to the slice site is additive on morphisms because it acts pointwise.
        intro φ ψ
        ext U u
        rfl
      map_smul' := by
        -- The same pointwise description shows compatibility with scalar multiplication.
        intro r φ
        -- Evaluate the restricted scalar multiple componentwise on each localized section.
        ext U u
        exact overMapPullback_map_smul_app_apply F G f r φ U u }
  map_id := by
    -- Restricting along the identity arrow leaves a local morphism unchanged.
    intro X
    ext φ U u
    exact congrArg (fun ψ ↦ ModuleCat.Hom.hom (ψ.hom.app U) u)
      (sheafHomModule_restrict_id F G X φ)
  map_comp := by
    -- Successive restrictions agree with restriction along the composite arrow.
    intro X Y Z f g
    ext φ U u
    exact congrArg (fun ψ ↦ ModuleCat.Hom.hom (ψ.hom.app U) u)
      (sheafHomModule_restrict_comp F G f g φ)

/-- The source-facing fixed-ring local-Hom presheaf satisfies the sheaf condition. -/
private theorem sheafHomModulePresheaf_isSheaf
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) :
    Presheaf.IsSheaf J (sheafHomModulePresheaf F G) := by
  -- Route correction: the earlier chapter owner file is currently broken, so this target keeps a
  -- local fallback owner. The next proof should still identify `sheafHomModulePresheaf F G` with
  -- the constant-ring specialization of that owner and transport the sheaf condition across the
  -- comparison once the fallback or owner is completed.
  sorry

/-- The source-facing sheaf `\mathcal H\!\mathit{om}_{\Lambda}(F, G)` of local
`\Lambda`-linear morphisms between two sheaves of `\Lambda`-modules. This is the fixed-ring
view bridge underlying the notation `ℋom[Λ](F, G)` for the canonical Chapter 18 local-Hom
owner. -/
abbrev sheafHomModule
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) : Sheaf J (ModuleCat.{max u v} Λ) :=
  ⟨sheafHomModulePresheaf F G, sheafHomModulePresheaf_isSheaf F G⟩

set_option quotPrecheck false in
notation:max "ℋom[" Λ "](" F ", " G ")" =>
  (show Sheaf _ (ModuleCat Λ) from sheafHomModule F G)

end HomSheaf

section HomSheafBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [CommRing Λ]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [HasWeakSheafify J RingCat.{max u v}]
variable [J.WEqualsLocallyBijective RingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]

/-- The source-facing fixed-ring local-Hom sheaf, viewed over the constant ring sheaf
`\underline{\Lambda}`, is isomorphic to the Chapter 18 owner
`PresheafOfModules.localHomSheaf` specialized via `Sheaf.toConstantModuleSheaf`.

This file keeps the comparison at the theorem-level owner `IsIsomorphic`, so the canonical
Chapter 18 local-Hom construction stays primary and no chosen concrete comparison `Iso` is added
to the public API. -/
theorem sheafHomModule_toConstantModuleSheaf_isomorphic_localHomSheaf
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) :
    let E :=
      (constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).app
        (CommRingCat.of Λ)
    IsIsomorphic
      ((ℋom[Λ](F, G)).toConstantModuleSheaf)
      ((SheafOfModules.restrictScalars E.inv).obj
        (PresheafOfModules.localHomSheaf
          ((constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of Λ))
          (((SheafOfModules.restrictScalars E.hom).obj F.toConstantModuleSheaf).val)
          ((SheafOfModules.restrictScalars E.hom).obj G.toConstantModuleSheaf))) :=
  by
  -- TODO: once the presheaf-level bridge is in place, package the resulting sheaf isomorphism as
  -- the proposition-level `IsIsomorphic` comparison stated here.
  sorry

end HomSheafBridge

section IsoSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [CommRing Λ]

/-- Helper for Lemma 18.43.4: restricting a local isomorphism along a slice pullback still gives
an isomorphism on the restricted sheaves. -/
private theorem overMapPullback_map_isIso
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ≅ G.over X.unop) :
    IsIso ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.hom) := by
  -- Functors preserve isomorphisms, so the restricted `hom` remains invertible.
  apply Functor.map_isIso

/-- Helper for Lemma 18.43.4: the restriction of a local isomorphism is the isomorphism induced
by restricting its `hom` field. -/
private def sheafIsoRestrict
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ≅ G.over X.unop) :
    F.over Y.unop ≅ G.over Y.unop :=
  @asIso _ _ _ _ ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.hom)
    (overMapPullback_map_isIso F G f φ)

/-- Restriction along the identity morphism acts trivially on local isomorphisms. -/
private theorem sheafIsoPresheaf_map_id
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) (X : Cᵒᵖ)
    (φ : F.over X.unop ≅ G.over X.unop) :
    sheafIsoRestrict F G (𝟙 X) φ = φ := by
  -- Route correction: define restriction of local isomorphisms through the mapped `hom` field,
  -- then the identity law is exactly the Hom-level restriction law.
  apply Iso.ext
  exact sheafHomModule_restrict_id F G X φ.hom

-- Proof sketch: restriction of local isomorphisms is functorial, so restricting first along `g`
-- and then along `f` agrees with restricting once along `f ≫ g`.
/-- Restriction of local isomorphisms is compatible with composition. -/
private theorem sheafIsoPresheaf_map_comp
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : F.over X.unop ≅ G.over X.unop) :
    sheafIsoRestrict F G (f ≫ g) φ =
      sheafIsoRestrict F G g (sheafIsoRestrict F G f φ) := by
  -- After replacing `mapIso` by `asIso` of the mapped `hom`, functoriality reduces to the
  -- Hom-level composition law.
  apply Iso.ext
  exact sheafHomModule_restrict_comp F G f g φ.hom

/-- Helper for Lemma 18.43.4: the forward map of a restricted local isomorphism is the restricted
forward map. -/
private theorem sheafIsoRestrict_hom
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ≅ G.over X.unop) :
    (sheafIsoRestrict F G f φ).hom =
      (J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.hom := by
  -- `sheafIsoRestrict` is defined by applying `asIso` to the restricted forward map.
  rfl

/-- Helper for Lemma 18.43.4: the inverse map of a restricted local isomorphism is the restricted
inverse map. -/
private theorem sheafIsoRestrict_inv
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (φ : F.over X.unop ≅ G.over X.unop) :
    (sheafIsoRestrict F G f φ).inv =
      (J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.inv := by
  -- Identify the inverse by checking that it composes with the restricted forward map to the
  -- identity.
  symm
  apply IsIso.eq_inv_of_hom_inv_id
  change
    ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.hom) ≫
        ((J.overMapPullback (ModuleCat.{max u v} Λ) f.unop).map φ.inv) =
      𝟙 _
  simpa using Functor.map_hom_inv_id (J.overMapPullback (ModuleCat.{max u v} Λ) f.unop) φ

/-- The source-facing presheaf of local isomorphisms between two sheaves of `\Lambda`-modules on
a site. This is a view layer over the canonical local-Hom/internal-Hom owners. -/
private def sheafIsoPresheaf
    (F G : Sheaf J (ModuleCat.{max u v} Λ)) : Cᵒᵖ ⥤ Type (max u v) where
  obj X := F.over X.unop ≅ G.over X.unop
  map f := sheafIsoRestrict F G f
  map_id := by
    intro X
    funext φ
    exact sheafIsoPresheaf_map_id F G X φ
  map_comp := by
    intro X Y Z f g
    funext φ
    exact sheafIsoPresheaf_map_comp F G f g φ

-- Proof sketch: local isomorphisms glue by applying the sheaf condition to the forward and
-- inverse morphisms and using uniqueness of gluing to preserve the inverse identities.
/-- The presheaf of local isomorphisms satisfies the sheaf condition. -/
private theorem sheafIsoPresheaf_isSheaf (F G : Sheaf J (ModuleCat.{max u v} Λ)) :
    Presheaf.IsSheaf J (sheafIsoPresheaf F G) := by
  -- TODO: the intended proof glues `hom` and `inv` families via the Hom-sheaf condition, but the
  -- current script is written against the wrong `Presheaf.IsSheaf` API. Rebuild it from the
  -- actual `Presieve.FamilyOfElements` interface exposed by the current mathlib version.
  sorry

/-- The source-facing sheaf of local isomorphisms between two sheaves of `\Lambda`-modules. -/
def sheafIso (F G : Sheaf J (ModuleCat.{max u v} Λ)) : Sheaf J (Type (max u v)) :=
  ⟨sheafIsoPresheaf F G, sheafIsoPresheaf_isSheaf F G⟩

end IsoSheaf

section MainStatements

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [CommRing Λ]

/-- Helper for Lemma 18.43.4: the sieve on `U` generated by a slice-site family is the sieve
generated by the corresponding underlying arrows in the ambient site. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type (max u v)} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  -- A factorization in the slice category forgets to the same factorization in the ambient site.
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Conversely, any ambient factorization lifts uniquely to the corresponding slice
    -- factorization.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 18.43.4: composing a slice-site cover of `U` with slice-site covers of each
member yields a sigma-indexed slice-site cover of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {ι : Type (max u v)} {X : ι → Over U}
    (hX : (J.over U).CoversTop X)
    {κ : ι → Type (max u v)} {Y : ∀ i : ι, κ i → Over (X i).left}
    (hY : ∀ i : ι, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma κ ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Convert both slice covers to ambient covering sieves and compose them using `bindOfArrows`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X).1 hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : ι,
        Sieve.ofArrows (fun a : κ i ↦ (Y i a).left) (fun a ↦ (Y i a).hom) ∈ J (X i).left := by
    intro i
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (J.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal) (Y i)).1 (hY i)
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hYTerminal
    exact hYTerminal
  -- Compose the two ambient covering sieves and rewrite the resulting generators back into the
  -- sigma-indexed family of composite slice arrows.
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦ Presieve.ofArrows (fun a : κ i ↦ (Y i a).left) (fun a ↦ (Y i a).hom))
      (fun i ↦ by simpa using hY' i)

section ConstantHom

variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]

-- Proof sketch: compare the source-facing fixed-ring object with the canonical owner from
-- `sheafHomModule_toConstantModuleSheaf_isomorphic_localHomSheaf`, apply the finite-presentation
-- comparison there, and transport back.
/-- Lemma 18.43.4 (1): if `M` is finitely presented, then the source-facing local-Hom sheaf
`\mathcal H\!\mathit{om}_{\Lambda}(\underline M, \underline N)` is isomorphic to the constant
sheaf on `\operatorname{Hom}_\Lambda(M, N)`. In the ambient universe this value is represented
by `ULift (M →ₗ[Λ] N)`.

This file keeps the statement at the proposition-level owner `IsIsomorphic`, rather than adding a
chosen concrete sheaf isomorphism to the public API. -/
theorem sheafHomModule_constantSheaf_isomorphic_of_finitePresentation
    (M N : ModuleCat.{max u v} Λ) [Module.FinitePresentation Λ M] :
    IsIsomorphic
      (ℋom[Λ](
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj M),
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj N)))
      ((constantSheaf J (ModuleCat.{max u v} Λ)).obj
        (ModuleCat.of Λ (ULift.{max u v} (M →ₗ[Λ] N)))) :=
  by
  -- TODO: prove the finite free source case explicitly, then compare both sides for a finite free
  -- presentation of `M` using the canonical local-Hom owner and exactness of the presentation.
  sorry

/-- Companion to Lemma 18.43.4 (1): the source-facing local-Hom sheaf for `\underline M` and
`\underline N` is constant. -/
theorem sheafHomModule_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{max u v} Λ) [Module.FinitePresentation Λ M] :
    Sheaf.IsConstant J
      (ℋom[Λ](
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj M),
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj N))) := by
  -- The comparison theorem already identifies the local-Hom sheaf with a constant sheaf.
  obtain ⟨e⟩ :=
    sheafHomModule_constantSheaf_isomorphic_of_finitePresentation (J := J) (M := M) (N := N)
  exact Sheaf.isConstant_of_iso (J := J) e

end ConstantHom

section ConstantIso

variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
variable [HasWeakSheafify J (Type (max u v))]
-- Proof sketch: after clause (1), the canonical local-Hom owner between `\underline M` and
-- `\underline N` is constant. The local isomorphism sheaf is cut out by the equations expressing
-- that a section and a candidate inverse compose to the identity, so it is again constant with
-- value `\operatorname{Isom}_\Lambda(M, N)`.
/-- Lemma 18.43.4 (2): if `M` and `N` are finitely presented, then the sheaf of local
isomorphisms between `\underline M` and `\underline N` is isomorphic to the constant sheaf with
value `\operatorname{Isom}_\Lambda(M, N)`. In the ambient universe this value is represented by
`ULift (M ≃ₗ[Λ] N)`.

This file again keeps only the proposition-level owner `IsIsomorphic` in the public API. -/
theorem sheafIso_constantSheaf_isomorphic_of_finitePresentation
    (M N : ModuleCat.{max u v} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    IsIsomorphic
      (sheafIso
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj N))
      ((constantSheaf J (Type (max u v))).obj (ULift.{max u v} (M ≃ₗ[Λ] N))) :=
  by
  -- TODO: identify a local isomorphism with a pair of local Hom sections, apply the constant
  -- Hom comparison in both directions, and use the inverse equations to recover a global linear
  -- equivalence.
  sorry

/-- Companion to Lemma 18.43.4 (2): the sheaf of local isomorphisms between `\underline M` and
`\underline N` is constant. -/
theorem sheafIso_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{max u v} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    Sheaf.IsConstant J
      (sheafIso
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v} Λ)).obj N)) := by
  -- The preceding isomorphism theorem turns the local-isomorphism sheaf into a constant sheaf.
  obtain ⟨e⟩ :=
    sheafIso_constantSheaf_isomorphic_of_finitePresentation (J := J) (M := M) (N := N)
  exact Sheaf.isConstant_of_iso (J := J) e

end ConstantIso

section LocallyConstantHom

variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v} Λ)]
variable [HasWeakSheafify J RingCat.{max u v}]
variable [J.WEqualsLocallyBijective RingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

-- Proof sketch: the assertion is local on the site. On a covering where `F` and `G` are
-- identified with constant sheaves, the intrinsic finite-presentation hypothesis on
-- `F` restricts to finite presentation of the local model, and the canonical Chapter 18
-- local-Hom comparison lets clause (1) be applied before returning to the fixed-ring view
-- `ℋom[Λ](F, G)`.
/-- Lemma 18.43.4 (3): if `\mathcal F` is a locally constant sheaf of `\Lambda`-modules of finite
presentation and `\mathcal G` is locally constant, then the local-Hom sheaf
`\mathcal H\!\mathit{om}_{\Lambda}(\mathcal F, \mathcal G)` is locally constant as a sheaf of
`\Lambda`-modules. -/
theorem sheafHomModule_isLocallyConstant_of_isFinitePresentation
    (F G : Sheaf J (ModuleCat.{max u v} Λ))
    [F.IsFinitePresentation]
    [Sheaf.IsLocallyConstant F]
    [Sheaf.IsLocallyConstant G] :
    Sheaf.IsLocallyConstant (ℋom[Λ](F, G)) := by
  -- TODO: refine the local constant charts of `F` and `G`, improve the chart for `F` to a
  -- finitely presented constant model, apply the constant-source theorem on each slice chart, and
  -- reassemble with `Sheaf.isLocallyConstant_of_explicit_constant_models`.
  sorry

end LocallyConstantHom

section LocallyConstantIso

variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v} Λ)]
variable [HasWeakSheafify J RingCat.{max u v}]
variable [J.WEqualsLocallyBijective RingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ X : C, (J.over X).HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J (Type (max u v))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v))]

-- Proof sketch: apply clause (3) in both directions to obtain local constancy of the forward and
-- reverse local-Hom objects. The local isomorphism sheaf is cut out by the equations expressing
-- that a section and its inverse compose to the identity, hence it is locally constant as well.
/-- Lemma 18.43.4 (4): if `\mathcal F` and `\mathcal G` are locally constant sheaves of
`\Lambda`-modules of finite presentation, then the sheaf of local isomorphisms
`\mathit{Isom}_{\underline{\Lambda}}(\mathcal F, \mathcal G)` is locally constant. -/
theorem sheafIso_isLocallyConstant_of_isFinitePresentation
    (F G : Sheaf J (ModuleCat.{max u v} Λ))
    [F.IsFinitePresentation]
    [G.IsFinitePresentation]
    [Sheaf.IsLocallyConstant F]
    [Sheaf.IsLocallyConstant G] :
    Sheaf.IsLocallyConstant (sheafIso F G) := by
  -- TODO: after proving local constancy of the forward and reverse local-Hom sheaves, construct
  -- local constant models for invertible sections by chartwise application of the constant
  -- isomorphism theorem and transport back along the chosen local charts.
  sorry

end LocallyConstantIso

end MainStatements

end CategoryTheory
