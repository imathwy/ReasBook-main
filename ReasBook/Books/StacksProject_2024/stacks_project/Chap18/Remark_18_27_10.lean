import Mathlib
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.stacks_project.Chap07.Lemma_7_30_3
import StacksProject_2024.stacks_project.Chap18.Definition_18_5_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal
open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.FreeAbelianSheaf

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Remark 18.27.10:
- primary domain: localization of sheaves along the category-of-elements projection, free abelian
  sheaves, and the canonical sheaf-level monoidal owner used to express tensoring by `j_! \mathbf
  Z`;
- sampled owner declarations:
  `localizationProjection`,
  `Functor.sheafPullback`,
  `(ℤ_ G)^#[J]`,
  `Sheaf.monoidalCategory`;
- best owner abstraction: this remark is a `bridge/view` statement. Its first clause compares the
  canonical lower-shriek owner
  `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`
  with the chapter's source-facing free-abelian-sheaf owner
  `((ℤ_ ℱ.obj)^#[J])`; its second clause uses the chosen sheaf
  monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`, rather than an arbitrary monoidal
  structure on abelian sheaves;
- primitive data: only the sheaf `ℱ`, the localized constant integer sheaf, the abelian sheaf
  `ℋ`, and the canonical localization functors;
- derived API: the canonical comparison isomorphism in part (a), the tensor-comparison morphism
  in part (b) built from the oplax monoidal structure on lower shriek and the adjunction counit,
  and the source-facing iso obtained by composing that comparison with the monoidal unitors. Any
  exact-interface wrapper around these owners would carry no extra mathematics.

Source/core/bridge triage:
- `source-facing`: the source remark identifying `j_! \mathbf Z` with the free abelian sheaf on
  `ℱ.obj`, and identifying `j_! j^{-1} \mathcal H` with `(j_! \mathbf Z) \otimes \mathcal H`;
- `core/canonical`: `localizationProjection`, `localizationTopology`,
  `Functor.sheafPullback`, `Functor.sheafPushforwardContinuous`,
  `(presheafToSheaf J AddCommGrpCat).obj (ℤ_ ℱ.obj)`, and `Sheaf.monoidalCategory`;
- `bridge/view`: the localized constant integer sheaf on the site of elements and the comparison
  morphisms built from the slice-topos equivalence, the free-abelian-sheaf adjunction, and the
  sheaf monoidal owner. -/

section Localization

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (ℱ : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).IsRightAdjoint]

local notation "ℤₗ" =>
  Functor.obj (constantSheaf (localizationTopology ℱ) AddCommGrpCat)
    (AddCommGrpCat.of (ULift ℤ))

private noncomputable def addCommGrpForgetCorepresentableByZ :
    (forget AddCommGrpCat.{v}).CorepresentableBy (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.CorepresentableBy.ofIso
    (Functor.CorepresentableBy.coyoneda (op (AddCommGrpCat.of (ULift.{v} ℤ))))
    AddCommGrpCat.coyonedaObjIsoForget

private noncomputable def addCommGrpForgetCorepresentableByFreePUnit :
    (forget AddCommGrpCat.{v}).CorepresentableBy (AddCommGrpCat.free.obj PUnit) where
  homEquiv {Y} := (AddCommGrpCat.adj.homEquiv PUnit Y).trans (Equiv.funUnique PUnit Y)
  homEquiv_comp {Y Y'} g f := by
    change ((AddCommGrpCat.adj.homEquiv PUnit Y') (f ≫ g)) PUnit.unit =
      (forget AddCommGrpCat.{v}).map g (((AddCommGrpCat.adj.homEquiv PUnit Y) f) PUnit.unit)
    simpa using congrFun (AddCommGrpCat.adj.homEquiv_naturality_right f g) PUnit.unit

private noncomputable def addCommGrpFreePUnitIsoZ :
    AddCommGrpCat.free.obj PUnit ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  Functor.CorepresentableBy.uniqueUpToIso
    (addCommGrpForgetCorepresentableByFreePUnit : _
      )
    (addCommGrpForgetCorepresentableByZ : _)

private noncomputable def localizationTerminalSheafOverTerminalIso :
    (sheafCategoryOfElementsEquivOver ℱ).functor.obj
        (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ≅
      Over.mk (𝟙 ℱ) :=
  (Functor.mapIso (sheafCategoryOfElementsEquivOver ℱ).functor
      (Limits.IsTerminal.uniqueUpToIso
        (Sheaf.isTerminalTerminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
        Limits.terminalIsTerminal)) ≪≫
    PreservesTerminal.iso (sheafCategoryOfElementsEquivOver ℱ).functor ≪≫
    Limits.IsTerminal.uniqueUpToIso Limits.terminalIsTerminal Over.mkIdTerminal

private noncomputable def localizationTerminalSheafToInverseImageEquiv
    (𝒢 : Sheaf J (Type v)) :
    ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).obj 𝒢) ≃
      (ℱ ⟶ 𝒢) :=
  let hFF :
      ((sheafCategoryOfElementsEquivOver ℱ).functor).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (sheafCategoryOfElementsEquivOver ℱ).functor
  let e₁ :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢) ≃
        ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          (sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).obj 𝒢)) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₂ :
      ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢)) ≃
        (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) :=
    (localizationTerminalSheafOverTerminalIso ℱ).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢)
  let e₃ : (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) ≃ (ℱ ⟶ 𝒢) :=
    ((Over.forgetAdjStar ℱ).homEquiv (Over.mk (𝟙 ℱ)) 𝒢).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Remark 18.27.10: the terminal-sheaf comparison for the localization at `ℱ` is
natural in the target sheaf. This is the right-naturality normalization needed in the Yoneda
comparison for part (a). -/
private theorem localizationTerminalSheafToInverseImageEquiv_naturality
    {𝒢 𝒢' : Sheaf J (Type v)} (g : 𝒢 ⟶ 𝒢')
    (f : (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
      ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
        (localizationTopology ℱ) J).obj 𝒢) :
    localizationTerminalSheafToInverseImageEquiv ℱ 𝒢'
        (f ≫ ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).map g) =
      localizationTerminalSheafToInverseImageEquiv ℱ 𝒢 f ≫ g := by
  -- Route correction: instead of unfolding the whole Yoneda chain at once, move `g` through the
  -- three owner equivalence legs separately: full faithfulness, the `Over.star` comparison, and
  -- the adjunction `Over.forget ⊣ Over.star`.
  let hFF :
      ((sheafCategoryOfElementsEquivOver ℱ).functor).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (sheafCategoryOfElementsEquivOver ℱ).functor
  let e₁ :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢) ≃
        ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          (sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).obj 𝒢)) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₁' :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢') ≃
        ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          (sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).obj 𝒢')) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₂ :
      ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢)) ≃
        (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) :=
    (localizationTerminalSheafOverTerminalIso ℱ).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢)
  let e₂' :
      ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢')) ≃
        (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢') :=
    (localizationTerminalSheafOverTerminalIso ℱ).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢')
  let e₃ : (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) ≃ (ℱ ⟶ 𝒢) :=
    ((Over.forgetAdjStar ℱ).homEquiv (Over.mk (𝟙 ℱ)) 𝒢).symm
  let e₃' : (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢') ≃ (ℱ ⟶ 𝒢') :=
    ((Over.forgetAdjStar ℱ).homEquiv (Over.mk (𝟙 ℱ)) 𝒢').symm
  change e₃' (e₂' (e₁' (f ≫ ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
    (localizationTopology ℱ) J).map g))) = e₃ (e₂ (e₁ f)) ≫ g
  -- First move `g` across the fully faithful equivalence to `Over ℱ`.
  rw [show e₁' (f ≫ ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
      (localizationTopology ℱ) J).map g) =
      e₁ f ≫ (sheafCategoryOfElementsEquivOver ℱ).functor.map
        (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).map g) from by
        simpa [e₁, e₁', Functor.FullyFaithful.homEquiv_apply, Category.assoc]]
  -- Next transport the codomain comparison from the category-of-elements model to `Over.star`.
  rw [show e₂' (e₁ f ≫ (sheafCategoryOfElementsEquivOver ℱ).functor.map
      (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
        (localizationTopology ℱ) J).map g)) =
      e₂ (e₁ f) ≫
        (((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).homCongr
          ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢'))
          ((sheafCategoryOfElementsEquivOver ℱ).functor.map
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).map g)) from by
        calc
          e₂' (e₁ f ≫ (sheafCategoryOfElementsEquivOver ℱ).functor.map
              (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
                (localizationTopology ℱ) J).map g)) =
              e₂ (e₁ f) ≫
                (((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢)
                  .homCongr
                    ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app
                      𝒢'))
                  ((sheafCategoryOfElementsEquivOver ℱ).functor.map
                    (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
                      (localizationTopology ℱ) J).map g)) := by
                simpa [e₂, e₂', Category.assoc] using
                  (Iso.homCongr_comp
                    (localizationTerminalSheafOverTerminalIso ℱ)
                    ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app
                      𝒢)
                    ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app
                      𝒢')
                    (e₁ f)
                    ((sheafCategoryOfElementsEquivOver ℱ).functor.map
                      (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
                        (localizationTopology ℱ) J).map g)))]
  rw [show (((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢'))
      ((sheafCategoryOfElementsEquivOver ℱ).functor.map
        (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).map g)) =
      (Over.star ℱ).map g from by
        change ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).inv ≫
            (sheafCategoryOfElementsEquivOver ℱ).functor.map
              (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
                (localizationTopology ℱ) J).map g) ≫
            ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢').hom =
          (Over.star ℱ).map g
        -- This is exactly the naturality of the comparison with `Over.star`.
        calc
          ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).inv ≫
              (sheafCategoryOfElementsEquivOver ℱ).functor.map
                (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
                  (localizationTopology ℱ) J).map g) ≫
              ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app
                𝒢').hom =
            ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).inv ≫
              ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢).hom ≫
                (Over.star ℱ).map g := by
                  simpa [Category.assoc] using
                    congrArg
                      (((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app
                        𝒢).inv ≫ ·)
                      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).hom
                        .naturality g)
          _ = (Over.star ℱ).map g := by simp]
  -- Finally move `g` through the adjunction `Over.forget ⊣ Over.star`.
  simpa [e₃, e₃'] using
    (Over.forgetAdjStar ℱ).homEquiv_naturality_right_symm (e₂ (e₁ f)) g

private noncomputable def localizedConstantIntegerIsoComposeAndSheafifyTerminal :
    ℤₗ ≅
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
        (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) :=
  let e :
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ≅
        (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.free.obj PUnit) := by
    simpa [Sheaf.composeAndSheafify, Sheaf.terminal, constantSheaf] using
      (Functor.mapIso (presheafToSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
        ((Functor.compConstIso _ AddCommGrpCat.free).symm.app PUnit))
  (Functor.mapIso (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
      addCommGrpFreePUnitIsoZ).symm ≪≫
    e.symm

end Localization

private noncomputable def freeAbelianSheafOnSheaf_composeAndSheafifyCorepresentable
    [HasWeakSheafify J AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v)) :
    (sheafForget J ⋙ coyoneda.obj (op ℱ)).CorepresentableBy
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) where
  homEquiv {Y} := (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv ℱ Y
  homEquiv_comp {Y Y'} g f := by
    simpa using
      congrArg (fun k ↦ k) ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_right f g)

/-- Helper for Remark 18.27.10: the source-facing free-abelian-sheaf Hom equivalence is natural
in the target sheaf. This is the fixed normalization used when the Yoneda proof pushes a
postcomposition map through sheafification, the free/forget adjunction, and full faithfulness of
`sheafToPresheaf`. -/
private theorem freeAbelianSheafOnSheaf_sourceFacing_homEquiv_naturality
    [HasWeakSheafify J AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v)) {Y Y' : Sheaf J AddCommGrpCat.{v}} (g : Y ⟶ Y')
    (f : (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ Y) :
    let hFF :
        (sheafToPresheaf J (Type v)).FullyFaithful :=
      Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf J (Type v))
    let eFF :
        (ℱ ⟶ (sheafForget J).obj Y) ≃
          (ℱ.obj ⟶ ((sheafForget J).obj Y).obj) :=
      Functor.FullyFaithful.homEquiv hFF
    let eFF' :
        (ℱ ⟶ (sheafForget J).obj Y') ≃
          (ℱ.obj ⟶ ((sheafForget J).obj Y').obj) :=
      Functor.FullyFaithful.homEquiv hFF
    let e₀ :
        ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ Y) ≃
          (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y.obj) :=
      (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv (ℱ.obj ⋙ AddCommGrpCat.free) Y
    let e₀' :
        ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ Y') ≃
          (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y'.obj) :=
      (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv (ℱ.obj ⋙ AddCommGrpCat.free) Y'
    let e₁ :
        (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y.obj) ≃
          (ℱ.obj ⟶ ((sheafForget J).obj Y).obj) :=
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv ℱ.obj Y.obj
    let e₁' :
        (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y'.obj) ≃
          (ℱ.obj ⟶ ((sheafForget J).obj Y').obj) :=
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv ℱ.obj Y'.obj
    eFF'.symm (e₁' (e₀' (f ≫ g))) =
      eFF.symm (e₁ (e₀ f)) ≫ (sheafForget J).map g := by
  -- Push the composite through the three equivalence legs used in the source-facing Hom-set
  -- description: sheafification, the presheaf free/forget adjunction, and full faithfulness of
  -- `sheafToPresheaf`.
  let hFF :
      (sheafToPresheaf J (Type v)).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf J (Type v))
  let eFF :
      (ℱ ⟶ (sheafForget J).obj Y) ≃
        (ℱ.obj ⟶ ((sheafForget J).obj Y).obj) :=
    Functor.FullyFaithful.homEquiv hFF
  let eFF' :
      (ℱ ⟶ (sheafForget J).obj Y') ≃
        (ℱ.obj ⟶ ((sheafForget J).obj Y').obj) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₀ :
      ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ Y) ≃
        (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y.obj) :=
    (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv (ℱ.obj ⋙ AddCommGrpCat.free) Y
  let e₀' :
      ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ Y') ≃
        (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y'.obj) :=
    (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv (ℱ.obj ⋙ AddCommGrpCat.free) Y'
  let e₁ :
      (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y.obj) ≃
        (ℱ.obj ⟶ ((sheafForget J).obj Y).obj) :=
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv ℱ.obj Y.obj
  let e₁' :
      (ℱ.obj ⋙ AddCommGrpCat.free ⟶ Y'.obj) ≃
        (ℱ.obj ⟶ ((sheafForget J).obj Y').obj) :=
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv ℱ.obj Y'.obj
  change eFF'.symm (e₁' (e₀' (f ≫ g))) =
    eFF.symm (e₁ (e₀ f)) ≫ (sheafForget J).map g
  -- First move `g` across the sheafification adjunction.
  rw [show e₀' (f ≫ g) = e₀ f ≫ g.hom from by
    exact (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_right f g]
  -- Next use right naturality of the presheaf free/forget adjunction.
  rw [show e₁' (e₀ f ≫ g.hom) = e₁ (e₀ f) ≫ ((sheafForget J).map g).hom from by
    exact ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right (e₀ f) g.hom)]
  -- Finally, identify the underlying presheaf composite with composition in the sheaf category.
  apply eFF'.injective
  simpa [Functor.FullyFaithful.homEquiv_apply, Category.assoc]

private noncomputable def freeAbelianSheafOnSheaf_sourceFacingCorepresentable
    [HasWeakSheafify J AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v)) :
    (sheafForget J ⋙ coyoneda.obj (op ℱ)).CorepresentableBy
      (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) where
  homEquiv {Y} :=
    let hFF :
        (sheafToPresheaf J (Type v)).FullyFaithful :=
      Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf J (Type v))
    let eFF :
        (ℱ ⟶ (sheafForget J).obj Y) ≃
          (ℱ.obj ⟶ ((sheafForget J).obj Y).obj) :=
      Functor.FullyFaithful.homEquiv hFF
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv (ℱ.obj ⋙ AddCommGrpCat.free) Y).trans
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv ℱ.obj Y.obj).trans
        eFF.symm)
  homEquiv_comp {Y Y'} g f := by
    -- Route correction: isolate the source-facing Hom-equivalence naturality as a reusable
    -- lemma, since the later Yoneda comparisons in Remark `18.27.10` need exactly the same
    -- normalization pattern.
    exact freeAbelianSheafOnSheaf_sourceFacing_homEquiv_naturality (J := J) ℱ g f

private noncomputable def freeAbelianSheafOnSheafIso
    [HasWeakSheafify J AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v)) :
    ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) ≅
      (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) :=
  Functor.CorepresentableBy.uniqueUpToIso
    (freeAbelianSheafOnSheaf_composeAndSheafifyCorepresentable ℱ)
    (freeAbelianSheafOnSheaf_sourceFacingCorepresentable ℱ)

section LocalizationComparison

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (ℱ : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).IsRightAdjoint]

local notation "jₗ!" =>
  Functor.sheafPullback (localizationProjection ℱ) AddCommGrpCat
    (localizationTopology ℱ) J
local notation "j⁻¹" =>
  Functor.sheafPushforwardContinuous (localizationProjection ℱ) AddCommGrpCat
    (localizationTopology ℱ) J
local notation "ℤₗ" =>
  Functor.obj (constantSheaf (localizationTopology ℱ) AddCommGrpCat)
    (AddCommGrpCat.of (ULift ℤ))

-- Proof sketch: identify the localization at `ℱ` with sheaves on the category of elements of
-- `ℱ`, use the adjunction for `(localizationProjection ℱ).sheafPullback AddCommGrpCat
-- (localizationTopology ℱ) J`, and compare the resulting Hom functor with the free-abelian-sheaf
-- adjunction of Lemma `18.5.2`. Yoneda then yields the canonical isomorphism.
/-- Helper for Remark 18.27.10: the Hom-set equivalence obtained by adjunction, the localized
free-abelian-sheaf identification of the constant integers, and the terminal-sheaf comparison. -/
private noncomputable def localization_constantInteger_lowerShriek_homEquiv
    (𝒢 : Sheaf J AddCommGrpCat.{v}) :
    (Functor.obj jₗ! ℤₗ ⟶ 𝒢) ≃
      (ℱ ⟶ (sheafForget J).obj 𝒢) :=
  let e₀ :
      (Functor.obj jₗ! ℤₗ ⟶ 𝒢) ≃
        (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢) :=
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv ℤₗ 𝒢
  let e₁ :
      (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢) ≃
        ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          Functor.obj j⁻¹ 𝒢) :=
    (localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ).homCongr (Iso.refl _)
  let e₂ :
      ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        Functor.obj j⁻¹ 𝒢) ≃
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢)) :=
    (Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj).homEquiv
      (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
      (Functor.obj j⁻¹ 𝒢)
  let e₃ :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢)) ≃
      (ℱ ⟶ (sheafForget J).obj 𝒢) :=
    by
      simpa using localizationTerminalSheafToInverseImageEquiv ℱ ((sheafForget J).obj 𝒢)
  e₀.trans (e₁.trans (e₂.trans e₃))

/-- Helper for Remark 18.27.10: the lower-shriek Hom equivalence for `j_! \mathbf Z` is natural in
the target sheaf. This is the remaining source-facing step needed to turn the Hom-chain into a
corepresentability statement. -/
private theorem localization_constantInteger_lowerShriek_homEquiv_naturality
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{v}} (g : 𝒢 ⟶ 𝒢')
    (f : Functor.obj jₗ! ℤₗ ⟶ 𝒢) :
    localization_constantInteger_lowerShriek_homEquiv (J := J) ℱ 𝒢' (f ≫ g) =
      localization_constantInteger_lowerShriek_homEquiv (J := J) ℱ 𝒢 f ≫ (sheafForget J).map g := by
  let e₀ :
      (Functor.obj jₗ! ℤₗ ⟶ 𝒢) ≃
        (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢) :=
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv ℤₗ 𝒢
  let e₀' :
      (Functor.obj jₗ! ℤₗ ⟶ 𝒢') ≃
        (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢') :=
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv ℤₗ 𝒢'
  let e₁ :
      (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢) ≃
        ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          Functor.obj j⁻¹ 𝒢) :=
    (localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ).homCongr (Iso.refl _)
  let e₁' :
      (ℤₗ ⟶ Functor.obj j⁻¹ 𝒢') ≃
        ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
            (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
          Functor.obj j⁻¹ 𝒢') :=
    (localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ).homCongr (Iso.refl _)
  let e₂ :
      ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        Functor.obj j⁻¹ 𝒢) ≃
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢)) :=
    (Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj).homEquiv
      (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
      (Functor.obj j⁻¹ 𝒢)
  let e₂' :
      ((Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        Functor.obj j⁻¹ 𝒢') ≃
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢')) :=
    (Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj).homEquiv
      (Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
      (Functor.obj j⁻¹ 𝒢')
  let e₃ :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢)) ≃
      (ℱ ⟶ (sheafForget J).obj 𝒢) :=
    by
      simpa using localizationTerminalSheafToInverseImageEquiv ℱ ((sheafForget J).obj 𝒢)
  let e₃' :
      ((Sheaf.terminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit) ⟶
        (sheafForget (localizationTopology ℱ)).obj (Functor.obj j⁻¹ 𝒢')) ≃
      (ℱ ⟶ (sheafForget J).obj 𝒢') :=
    by
      simpa using localizationTerminalSheafToInverseImageEquiv ℱ ((sheafForget J).obj 𝒢')
  change e₃' (e₂' (e₁' (e₀' (f ≫ g)))) =
    e₃ (e₂ (e₁ (e₀ f))) ≫ (sheafForget J).map g
  -- Move `g` through the localization adjunction first.
  rw [show e₀' (f ≫ g) = e₀ f ≫ (j⁻¹).map g from by
        exact ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (localizationTopology ℱ) J).homEquiv_naturality_right f g]
  -- Then transport across the fixed identification of the localized constant integer sheaf.
  rw [show e₁' (e₀ f ≫ (j⁻¹).map g) = e₁ (e₀ f) ≫ (j⁻¹).map g from by
        simpa [e₁, e₁'] using
          (Iso.homCongr_comp (localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ)
            (Iso.refl (Functor.obj j⁻¹ 𝒢))
            (Iso.refl (Functor.obj j⁻¹ 𝒢'))
            (e₀ f) ((j⁻¹).map g))]
  -- Next apply right naturality of the free/forget adjunction on the localized site.
  rw [show e₂' (e₁ (e₀ f) ≫ (j⁻¹).map g) =
      e₂ (e₁ (e₀ f)) ≫ (sheafForget (localizationTopology ℱ)).map ((j⁻¹).map g) from by
        exact (Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj)
          .homEquiv_naturality_right (e₁ (e₀ f)) ((j⁻¹).map g)]
  -- The last step is exactly the terminal-sheaf naturality proved above on the underlying
  -- sheaves of sets.
  simpa [e₃, e₃'] using
    localizationTerminalSheafToInverseImageEquiv_naturality (J := J) (ℱ := ℱ)
      ((sheafForget J).map g) (e₂ (e₁ (e₀ f)))

/-- Helper for Remark 18.27.10: the lower shriek of the localized constant integer sheaf
corepresents the source-facing Hom functor `𝒢 ↦ (ℱ ⟶ (sheafForget J).obj 𝒢)`. -/
private noncomputable def localization_constantInteger_lowerShriek_corepresentable
    :
    (sheafForget J ⋙ coyoneda.obj (op ℱ)).CorepresentableBy
      (Functor.obj jₗ! ℤₗ) where
  homEquiv {𝒢} := localization_constantInteger_lowerShriek_homEquiv (J := J) ℱ 𝒢
  homEquiv_comp {𝒢 𝒢'} g f :=
    localization_constantInteger_lowerShriek_homEquiv_naturality (J := J) (ℱ := ℱ) g f

private noncomputable def localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom
    :
    Functor.obj jₗ! ℤₗ ⟶
      (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) :=
  (Functor.CorepresentableBy.uniqueUpToIso
      (localization_constantInteger_lowerShriek_corepresentable (J := J) ℱ)
      (freeAbelianSheafOnSheaf_sourceFacingCorepresentable (J := J) ℱ)).hom

private instance localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_isIso
    : IsIso (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom ℱ) := by
  -- Route correction: package the source Yoneda proof as uniqueness of a corepresenting object.
  change IsIso
    ((Functor.CorepresentableBy.uniqueUpToIso
      (localization_constantInteger_lowerShriek_corepresentable (J := J) ℱ)
      (freeAbelianSheafOnSheaf_sourceFacingCorepresentable (J := J) ℱ)).hom)
  infer_instance

/-- Remark 18.27.10: for a sheaf of sets `ℱ` on `(C, J)`, the lower shriek of the constant
integer sheaf along the localization at `ℱ` is canonically isomorphic to the free abelian sheaf
generated by the underlying presheaf `ℱ.obj`; this is the statement
`j_! \mathbf Z = \mathbf Z_\mathcal F^\#`. -/
noncomputable abbrev localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf
    :
    Functor.obj jₗ! ℤₗ ≅
      (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) :=
  asIso (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom ℱ)

end LocalizationComparison

private def addCommGrpMonoidalEquiv :
    ModuleCat.{v} (ULift.{v} ℤ) ≌ AddCommGrpCat.{v} :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ)).symm.trans
    (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence

private abbrev addCommGrpMonoidalCategory :
    MonoidalCategory AddCommGrpCat.{v} :=
  Monoidal.transport (addCommGrpMonoidalEquiv : ModuleCat.{v} (ULift.{v} ℤ) ≌ AddCommGrpCat.{v})

-- Proof sketch: use the adjunction for
-- `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`, identify
-- morphisms out of the left-hand side with morphisms from `j_! \mathbf Z` into the internal Hom
-- sheaf by the canonical tensor-internal-Hom adjunction
-- `MonoidalClosed.internalHomAdjunction₂`, and conclude by Yoneda exactly as in the textbook
-- argument.
section Monoidal

attribute [local instance] Sheaf.monoidalCategory
attribute [local instance] addCommGrpMonoidalCategory

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
variable (ℱ : Sheaf J (Type v))
variable [((localizationTopology ℱ).W :
  MorphismProperty (ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ AddCommGrpCat.{v})).IsMonoidal]
variable [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).IsRightAdjoint]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).LaxMonoidal]

local notation "jₗ!" =>
  Functor.sheafPullback (localizationProjection ℱ) AddCommGrpCat
    (localizationTopology ℱ) J
local notation "j⁻¹" =>
  Functor.sheafPushforwardContinuous (localizationProjection ℱ) AddCommGrpCat
    (localizationTopology ℱ) J
local notation "ℤₗ" =>
  Functor.obj (constantSheaf (localizationTopology ℱ) AddCommGrpCat)
    (AddCommGrpCat.of (ULift ℤ))

private noncomputable def constantIntegerSheafLeftUnitor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [HasWeakSheafify K AddCommGrpCat.{v}]
    [((K.W : MorphismProperty (Dᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
    (𝒢 : Sheaf K AddCommGrpCat.{v}) :
    (((constantSheaf K AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) ⊗ 𝒢) ≅ 𝒢 :=
  show MonoidalCategoryStruct.tensorObj
      ((constantSheaf K AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) 𝒢 ≅ 𝒢 from
    MonoidalCategory.tensorIso
        (Functor.Monoidal.εIso (presheafToSheaf K AddCommGrpCat)).symm
        (Iso.refl 𝒢) ≪≫
      λ_ 𝒢

/-- Helper for Remark 18.27.10: the inverse-image/internal-Hom comparison attached to the
localization inverse-image functor. This is the source-faithful comparison used in part (b) after
currying the pullback of evaluation through the lax monoidal structure on `j⁻¹`. -/
private noncomputable abbrev localization_inverseImage_internalHom_comparison
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢) ⟶
      (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢) :=
  MonoidalClosed.curry
    (μ (j⁻¹) ℋ ((ihom ℋ).obj 𝒢) ≫
      (j⁻¹).map ((ihom.ev ℋ).app 𝒢))

/-- Helper for Remark 18.27.10: uncurrying the localization inverse-image/internal-Hom comparison
recovers the pullback of evaluation preceded by the lax monoidal tensor map of `j⁻¹`. -/
private theorem uncurry_localization_inverseImage_internalHom_comparison
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    MonoidalClosed.uncurry
        (localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ) ℋ 𝒢) =
      μ (j⁻¹) ℋ ((ihom ℋ).obj 𝒢) ≫
        (j⁻¹).map ((ihom.ev ℋ).app 𝒢) := by
  -- This is the defining computation rule for the comparison morphism.
  simp [localization_inverseImage_internalHom_comparison]

/-- Helper for Remark 18.27.10: the localization inverse-image/internal-Hom comparison is natural
in the target sheaf. This isolates the evaluation-side transport that remains in the proof of part
(b). -/
private theorem localization_inverseImage_internalHom_comparison_naturality
    (ℋ : Sheaf J AddCommGrpCat.{v}) {𝒢 𝒢' : Sheaf J AddCommGrpCat.{v}} (g : 𝒢 ⟶ 𝒢') :
    localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ) ℋ 𝒢 ≫
        (ihom (Functor.obj j⁻¹ ℋ)).map ((j⁻¹).map g) =
      (j⁻¹).map ((ihom ℋ).map g) ≫
        localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ) ℋ 𝒢' := by
  -- Route correction: keep the source proof's internal-Hom comparison explicit and prove its
  -- naturality by uncurrying, rather than hiding the transport inside a large final simp.
  apply MonoidalClosed.uncurry_injective
  -- Move `g` through the internal-Hom adjunction on each side of the equality.
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left]
  -- Now both sides are concrete composites built from `μ` and evaluation.
  rw [uncurry_localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ)]
  rw [uncurry_localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ)]
  -- First transport along the lax monoidal comparison `μ`.
  rw [μ_natural_right_assoc]
  -- Then use naturality of evaluation and map the resulting identity through `j⁻¹`.
  simpa [Functor.map_comp, Category.assoc] using
    congrArg ((j⁻¹).map) (ihom.ev_naturality (A := ℋ) g)

-- Proof sketch: this is the canonical tensor-comparison morphism for the lower shriek
-- `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`, namely the
-- oplax monoidal morphism `δ` evaluated at the constant integer sheaf and `j^{-1}\mathcal H`,
-- followed by tensoring with the adjunction counit `j_! j^{-1}\mathcal H ⟶ \mathcal H`.
local instance :
    (jₗ!).OplaxMonoidal :=
  ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (localizationTopology ℱ) J).leftAdjointOplaxMonoidal

-- Proof sketch: as in Lemma `18.27.9`, apply Yoneda to the canonical tensor-comparison morphism
-- above. For every target `\mathcal G`, the adjunction `j_! ⊣ j^{-1}`, the tensor-internal-Hom
-- adjunction on the sheaf categories, and the identification of `j_! \mathbf Z` from part (a)
-- identify postcomposition with this morphism with a chain of Hom-set equivalences. Hence the
-- comparison morphism is invertible.
/-- Remark 18.27.10 (b), owner form: the canonical tensor-comparison morphism
`j_!(\mathbf Z \otimes j^{-1}\mathcal H) ⟶ j_!\mathbf Z ⊗ \mathcal H`
is an isomorphism. -/
noncomputable def localization_lowerShriek_inverseImage_tensorComparison
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶
      ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) :=
  letI : MonoidalCategory (Sheaf J AddCommGrpCat.{v}) := Sheaf.monoidalCategory J AddCommGrpCat
  letI : MonoidalCategory (Sheaf (localizationTopology ℱ) AddCommGrpCat.{v}) :=
    Sheaf.monoidalCategory (localizationTopology ℱ) AddCommGrpCat
  let tensorCounit :
      ((Functor.obj jₗ! ℤₗ) ⊗ Functor.obj jₗ! (Functor.obj j⁻¹ ℋ)) ⟶
        ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) :=
    show MonoidalCategoryStruct.tensorObj (Functor.obj jₗ! ℤₗ)
        (Functor.obj jₗ! (Functor.obj j⁻¹ ℋ)) ⟶
      MonoidalCategoryStruct.tensorObj (Functor.obj jₗ! ℤₗ) ℋ from
      (𝟙 _) ⊗ₘ (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (localizationTopology ℱ) J).counit.app ℋ)
  let comparison :
      Functor.obj jₗ! (MonoidalCategoryStruct.tensorObj ℤₗ (Functor.obj j⁻¹ ℋ)) ⟶
        MonoidalCategoryStruct.tensorObj (Functor.obj jₗ! ℤₗ) ℋ :=
    δ jₗ! ℤₗ (Functor.obj j⁻¹ ℋ) ≫
      tensorCounit
  show Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) from
    comparison

/-- Helper for Remark 18.27.10: the source Hom-chain for part (b), stopping at morphisms out of
`j_! \mathbf Z`. This packages adjunction, the braided tensor/internal-Hom equivalence, the
localization/internal-Hom comparison, and adjunction back into one reusable equivalence. -/
private noncomputable def localization_lowerShriek_inverseImage_tensor_homEquiv
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    (Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) ≃
      (Functor.obj jₗ! ℤₗ ⟶ (ihom ℋ).obj 𝒢) :=
  let e₀ :
      (Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) ≃
        ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) :=
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) 𝒢
  let e₁ :
      ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) ≃
        (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) :=
    MonoidalClosed.braidedHomEquiv ℤₗ (Functor.obj j⁻¹ ℋ) (Functor.obj j⁻¹ 𝒢)
  let e₂ :
      (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) ≃
        (ℤₗ ⟶ Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢)) :=
    (Iso.refl _).homCongr
      (asIso (localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ) ℋ 𝒢)).symm
  let e₃ :
      (ℤₗ ⟶ Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢)) ≃
        (Functor.obj jₗ! ℤₗ ⟶ (ihom ℋ).obj 𝒢) :=
    (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv ℤₗ ((ihom ℋ).obj 𝒢)).symm
  e₀.trans (e₁.trans (e₂.trans e₃))

/-- Helper for Remark 18.27.10: applying the outer localization adjunction to the source
Hom-chain for part (b) removes exactly the final transport back from `j_! \mathbf Z`. This
packages the first normalization step in the source-faithful Yoneda comparison. -/
private theorem localization_lowerShriek_inverseImage_tensor_homEquiv_outer_adjunction
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v})
    (m : Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) :
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (localizationTopology ℱ) J).homEquiv ℤₗ ((ihom ℋ).obj 𝒢)
        (localization_lowerShriek_inverseImage_tensor_homEquiv (J := J) (ℱ := ℱ) ℋ 𝒢 m) =
      let e₀ :
          (Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) ≃
            ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) :=
        ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (localizationTopology ℱ) J).homEquiv (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) 𝒢
      let e₁ :
          ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) ≃
            (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) :=
        MonoidalClosed.braidedHomEquiv ℤₗ (Functor.obj j⁻¹ ℋ) (Functor.obj j⁻¹ 𝒢)
      let e₂ :
          (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) ≃
            (ℤₗ ⟶ Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢)) :=
        (Iso.refl _).homCongr
          (asIso (localization_inverseImage_internalHom_comparison
            (J := J) (ℱ := ℱ) ℋ 𝒢)).symm
      e₂ (e₁ (e₀ m)) := by
  -- Proof comment: the outer adjunction equivalence is the inverse of the final leg in
  -- `localization_lowerShriek_inverseImage_tensor_homEquiv`.
  simp [localization_lowerShriek_inverseImage_tensor_homEquiv]

/-- Helper for Remark 18.27.10: the outer adjunction leg in the source Hom-chain for part (b) is
natural in the target morphism. This packages the first postcomposition rewrite used in the
direct comparison with the tensor/internal-Hom equivalence. -/
private theorem localization_lowerShriek_inverseImage_tensor_outer_adjunction_naturality
    {𝒢 𝒢' : Sheaf J AddCommGrpCat.{v}}
    (ℋ : Sheaf J AddCommGrpCat.{v})
    (g : 𝒢 ⟶ 𝒢')
    (m : Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) :
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (localizationTopology ℱ) J).homEquiv (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) 𝒢'
        (m ≫ g) =
      ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (localizationTopology ℱ) J).homEquiv (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) 𝒢 m ≫
        (j⁻¹).map g := by
  -- Proof comment: this is exactly right-naturality of the localization adjunction.
  simpa using
    (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv_naturality_right m g)

/-- Helper for Remark 18.27.10: adjoining the part (a) identification of `j_! \mathbf Z` turns
the source Hom-chain for part (b) into an equivalence with morphisms out of the free abelian sheaf
on `ℱ`. This is the exact Yoneda target used in the final comparison argument. -/
private noncomputable def localization_lowerShriek_inverseImage_tensor_freeAbelianHomEquiv
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    (Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) ≃
      ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ (ihom ℋ).obj 𝒢) :=
  (localization_lowerShriek_inverseImage_tensor_homEquiv (J := J) (ℱ := ℱ) ℋ 𝒢).trans
    ((localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf (J := J) ℱ).homCongr
      (Iso.refl _))

/-- Helper for Remark 18.27.10: the target Hom-chain for part (b), obtained from the braided
tensor/internal-Hom equivalence on sheaves together with the part (a) identification
`j_! \mathbf Z \cong \mathbf Z_\mathcal F^\#`. This is the Yoneda target on morphisms out of
`j_! \mathbf Z \otimes \mathcal H`. -/
private noncomputable def localization_lowerShriek_tensor_freeAbelianHomEquiv
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    (((Functor.obj jₗ! ℤₗ) ⊗ ℋ) ⟶ 𝒢) ≃
      ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ (ihom ℋ).obj 𝒢) :=
  (MonoidalClosed.braidedHomEquiv (Functor.obj jₗ! ℤₗ) ℋ 𝒢).trans
    ((localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf (J := J) ℱ).homCongr
      (Iso.refl _))

/-- Helper for Remark 18.27.10: postcomposition with the part (a) comparison
`j_! \mathbf Z \to \mathbf Z_\mathcal F^\#` is bijective on morphisms into any internal-Hom
target. This isolates the formal Yoneda finish from the remaining transport calculation. -/
private theorem localization_constantInteger_postcompose_bijective_internalHom
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v}) :
    Function.Bijective
      (fun k : (((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ (ihom ℋ).obj 𝒢 ↦
        localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom (J := J) ℱ ≫ k) := by
  constructor
  · intro k₁ k₂ h
    -- Since the part (a) comparison is an isomorphism, it is mono, so postcomposition is
    -- injective on each target.
    exact
      (cancel_mono
        (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom (J := J) ℱ)).1 h
  · intro k
    -- Surjectivity is given by postcomposing with the inverse of the part (a) isomorphism.
    refine
      ⟨inv (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_hom (J := J) ℱ) ≫
          k, ?_⟩
    simp [Category.assoc]

/-- Helper for Remark 18.27.10: the source Hom-chain for `j_!(\mathbf Z \otimes j^{-1}\mathcal H)`
agrees directly with the braided tensor/internal-Hom equivalence after postcomposing by the
canonical tensor comparison. This is the source-faithful core identity before transporting across
part (a). -/
private theorem localization_lowerShriek_inverseImage_tensor_homEquiv_postcompose_eq_braidedHomEquiv
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v})
    (f : ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) ⟶ 𝒢) :
    localization_lowerShriek_inverseImage_tensor_homEquiv (J := J) (ℱ := ℱ) ℋ 𝒢
      (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ f) =
    MonoidalClosed.braidedHomEquiv (Functor.obj jₗ! ℤₗ) ℋ 𝒢 f := by
  let e₀ :
      (Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ 𝒢) ≃
        ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) :=
    ((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) 𝒢
  let e₁ :
      ((ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ⟶ Functor.obj j⁻¹ 𝒢) ≃
        (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) :=
    MonoidalClosed.braidedHomEquiv ℤₗ (Functor.obj j⁻¹ ℋ) (Functor.obj j⁻¹ 𝒢)
  let e₂ :
      (ℤₗ ⟶ (ihom (Functor.obj j⁻¹ ℋ)).obj (Functor.obj j⁻¹ 𝒢)) ≃
        (ℤₗ ⟶ Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢)) :=
    (Iso.refl _).homCongr
      (asIso (localization_inverseImage_internalHom_comparison (J := J) (ℱ := ℱ) ℋ 𝒢)).symm
  let e₃ :
      (ℤₗ ⟶ Functor.obj j⁻¹ ((ihom ℋ).obj 𝒢)) ≃
        (Functor.obj jₗ! ℤₗ ⟶ (ihom ℋ).obj 𝒢) :=
    (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv ℤₗ ((ihom ℋ).obj 𝒢)).symm
  -- Route correction: expose the four Hom-equivalence legs from the Yoneda proof so the final
  -- comparison is normalized before the part-(a) transport.
  change e₃ (e₂ (e₁ (e₀ (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ f)))) =
    MonoidalClosed.braidedHomEquiv (Functor.obj jₗ! ℤₗ) ℋ 𝒢 f
  -- Apply the outer adjunction first; the remaining identity lives entirely over the localized
  -- site and can be attacked by the tensor/internal-Hom adjunction.
  apply e₃.injective
  have h₀ :
      e₀ (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ f) =
        (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (localizationTopology ℱ) J).homEquiv
            (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ((Functor.obj jₗ! ℤₗ) ⊗ ℋ)
            (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ)) ≫
          (j⁻¹).map f := by
    -- First move the target morphism `f` across the outer localization adjunction.
    simpa [e₀] using
      (localization_lowerShriek_inverseImage_tensor_outer_adjunction_naturality
        (J := J) (ℱ := ℱ) (ℋ := ℋ) (g := f)
        (m := localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ))
  rw [h₀]
  -- TODO: after removing `e₃`, normalize the localized-side map by `MonoidalClosed.uncurry`,
  -- rewrite postcomposition with the inverse-image/internal-Hom comparison using
  -- `uncurry_localization_inverseImage_internalHom_comparison`, and use the oplax monoidal
  -- naturality of `δ` together with counit naturality to identify both composites.
  sorry

/-- Helper for Remark 18.27.10: the source Hom-chain for `j_!(\mathbf Z \otimes j^{-1}\mathcal H)`
and the target Hom-chain for `j_! \mathbf Z \otimes \mathcal H` agree after postcomposing with the
canonical tensor comparison. This is the source-faithful compatibility that closes the Yoneda
argument for part (b). -/
private theorem localization_lowerShriek_inverseImage_tensor_postcompose_eq_via_internalHom_comparison
    (ℋ 𝒢 : Sheaf J AddCommGrpCat.{v})
    (f : ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) ⟶ 𝒢) :
    localization_lowerShriek_inverseImage_tensor_freeAbelianHomEquiv (J := J) (ℱ := ℱ) ℋ 𝒢
      (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ f) =
    localization_lowerShriek_tensor_freeAbelianHomEquiv (J := J) (ℱ := ℱ) ℋ 𝒢 f := by
  -- The free-abelian target is only the final part-(a) transport; the source-faithful work is the
  -- direct compatibility on morphisms out of `j_! \mathbf Z`.
  let e :
      (Functor.obj jₗ! ℤₗ ⟶ (ihom ℋ).obj 𝒢) ≃
        ((((ℤ_ ℱ.obj)^#[J] : Sheaf J AddCommGrpCat.{v})) ⟶ (ihom ℋ).obj 𝒢) :=
    (localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf (J := J) ℱ).homCongr
      (Iso.refl _)
  -- Apply the part-(a) `homCongr` equivalence to the direct comparison proved above.
  simpa [localization_lowerShriek_inverseImage_tensor_freeAbelianHomEquiv,
    localization_lowerShriek_tensor_freeAbelianHomEquiv, e] using
    congrArg e
      (localization_lowerShriek_inverseImage_tensor_homEquiv_postcompose_eq_braidedHomEquiv
        (J := J) (ℱ := ℱ) ℋ 𝒢 f)

theorem localization_lowerShriek_inverseImage_tensorComparison_isIso
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    IsIso (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ) := by
  -- Route correction: the Yoneda proof compares the Hom-set out of the source of the tensor
  -- comparison with the Hom-set out of its target through two parallel source-faithful
  -- equivalence chains landing in the same internal-Hom target.
  refine isIso_of_yoneda_map_bijective _ (fun 𝒢 ↦ ?_)
  let Eₛ :=
    localization_lowerShriek_inverseImage_tensor_freeAbelianHomEquiv
      (J := J) (ℱ := ℱ) ℋ 𝒢
  let Eₜ :=
    localization_lowerShriek_tensor_freeAbelianHomEquiv
      (J := J) (ℱ := ℱ) ℋ 𝒢
  constructor
  · intro f g hfg
    have hf :
        Eₛ (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ f) = Eₜ f := by
      simpa [Eₛ, Eₜ] using
        localization_lowerShriek_inverseImage_tensor_postcompose_eq_via_internalHom_comparison
          (J := J) (ℱ := ℱ) ℋ 𝒢 f
    have hg :
        Eₛ (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ ≫ g) = Eₜ g := by
      simpa [Eₛ, Eₜ] using
        localization_lowerShriek_inverseImage_tensor_postcompose_eq_via_internalHom_comparison
          (J := J) (ℱ := ℱ) ℋ 𝒢 g
    -- Apply the target Hom-equivalence and reduce injectivity to equality in the common
    -- free-abelian/internal-Hom target.
    apply Eₜ.injective
    simpa [hf, hg] using congrArg Eₛ hfg
  · intro f
    refine ⟨Eₜ.symm (Eₛ f), ?_⟩
    -- The compatibility of the two source-faithful Hom-chains identifies the chosen preimage
    -- with the prescribed source morphism.
    apply Eₛ.injective
    simpa [Eₛ, Eₜ] using
      localization_lowerShriek_inverseImage_tensor_postcompose_eq_via_internalHom_comparison
        (J := J) (ℱ := ℱ) ℋ 𝒢 (Eₜ.symm (Eₛ f))

private noncomputable def localization_lowerShriek_inverseImage_tensorIso
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    Functor.obj jₗ! (ℤₗ ⊗ Functor.obj j⁻¹ ℋ) ≅ ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) := by
  let _ : IsIso (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ) :=
    localization_lowerShriek_inverseImage_tensorComparison_isIso ℱ ℋ
  exact asIso (localization_lowerShriek_inverseImage_tensorComparison ℱ ℋ)

/-- Remark 18.27.10 (b): for an abelian sheaf `ℋ`, localization followed by lower shriek is
canonically isomorphic to tensoring `ℋ` by `j_! \mathbf Z` in the canonical sheaf tensor product.
This is the source-facing iso obtained from the canonical tensor comparison morphism by the
left-unitor identification
`\mathbf Z \otimes j^{-1}\mathcal H \cong j^{-1}\mathcal H`. -/
noncomputable abbrev localization_lowerShriek_inverseImage_tensorConstantIntegerIso
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    Functor.obj jₗ! (Functor.obj j⁻¹ ℋ) ≅
      ((Functor.obj jₗ! ℤₗ) ⊗ ℋ) :=
  Functor.mapIso jₗ! ((constantIntegerSheafLeftUnitor (Functor.obj j⁻¹ ℋ)).symm) ≪≫
    localization_lowerShriek_inverseImage_tensorIso ℱ ℋ

end Monoidal

end CategoryTheory
