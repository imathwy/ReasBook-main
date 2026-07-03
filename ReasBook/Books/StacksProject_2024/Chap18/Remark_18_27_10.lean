import Mathlib
import StacksProject_2024.Chap07.Lemma_7_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory
open Opposite
open CategoryTheory.Limits

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
  `Sheaf.composeAndSheafify`,
  `Sheaf.monoidalCategory`;
- best owner abstraction: this remark is a `bridge/view` statement. Its first clause compares the
  canonical lower-shriek owner
  `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`
  with the canonical free-abelian-sheaf owner
  `Sheaf.composeAndSheafify J AddCommGrpCat.free`; its second clause uses the chosen sheaf
  monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`, rather than an arbitrary monoidal
  structure on abelian sheaves;
- primitive data: only the sheaf `ℱ`, the localized constant integer sheaf, the abelian sheaf
  `ℋ`, and the canonical localization functors;
- derived API: the two comparison isomorphism statements below. Any exact-interface wrapper around
  these owners would carry no extra mathematics.

Source/core/bridge triage:
- `source-facing`: the source remark identifying `j_! \mathbf Z` with the free abelian sheaf on
  `ℱ`, and identifying `j_! j^{-1} \mathcal H` with `(j_! \mathbf Z) \otimes \mathcal H`;
- `core/canonical`: `localizationProjection`, `localizationTopology`,
  `Functor.sheafPullback`, `Functor.sheafPushforwardContinuous`,
  `Sheaf.composeAndSheafify`, and `Sheaf.monoidalCategory`;
- `bridge/view`: the private short names `jShriek`, `jStar`, and `jShriekInteger`, used only to
  present the source-facing `j_!` surface without introducing a parallel public owner. -/

section Localization

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (ℱ : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).IsRightAdjoint]

private abbrev jShriek :
    Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v} :=
  (localizationProjection ℱ).sheafPullback AddCommGrpCat.{v} (localizationTopology ℱ) J

private abbrev jStar :
    Sheaf J AddCommGrpCat.{v} ⥤ Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} :=
  (localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
    (localizationTopology ℱ) J

private abbrev localizedConstantIntegerSheaf :
    Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} :=
  (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of (ULift.{v} ℤ))

private abbrev jShriekInteger : Sheaf J AddCommGrpCat.{v} :=
  (jShriek ℱ).obj (localizedConstantIntegerSheaf ℱ)

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

private noncomputable def localizationConstSingletonIsoChosenTerminal
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
      (⊤_ (Sheaf (localizationTopology ℱ) (Type v))) :=
  (sheafificationIso (Sheaf.terminal (localizationTopology ℱ)
      Limits.Types.isTerminalPUnit)).symm ≪≫
    Limits.IsTerminal.uniqueUpToIso
      (Sheaf.isTerminalTerminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
      Limits.terminalIsTerminal

private noncomputable def localizationConstSingletonOverTerminalIso
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    (sheafCategoryOfElementsEquivOver ℱ).functor.obj
        ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
      Over.mk (𝟙 ℱ) :=
  (Functor.mapIso (sheafCategoryOfElementsEquivOver ℱ).functor
      (localizationConstSingletonIsoChosenTerminal ℱ)) ≪≫
    PreservesTerminal.iso (sheafCategoryOfElementsEquivOver ℱ).functor ≪≫
    Limits.IsTerminal.uniqueUpToIso Limits.terminalIsTerminal Over.mkIdTerminal

private noncomputable def localizationConstSingletonToInverseImageEquiv
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    (𝒢 : Sheaf J (Type v)) :
    (((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).obj 𝒢) ≃
      (ℱ ⟶ 𝒢) :=
  let hFF :
      ((sheafCategoryOfElementsEquivOver ℱ).functor).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (sheafCategoryOfElementsEquivOver ℱ).functor
  let e₁ :
      (((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
          ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢) ≃
        ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
            ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
          (sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).obj 𝒢)) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₂ :
      ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
        (sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢)) ≃
        (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) :=
    (localizationConstSingletonOverTerminalIso ℱ).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢)
  let e₃ : (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) ≃ (ℱ ⟶ 𝒢) :=
    ((Over.forgetAdjStar ℱ).homEquiv (Over.mk (𝟙 ℱ)) 𝒢).symm
  e₁.trans (e₂.trans e₃)

private noncomputable def localizedConstantIntegerIsoComposeAndSheafifyTerminal
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    (localizedConstantIntegerSheaf ℱ) ≅
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
        ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) :=
  let e :
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
        (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.free.obj PUnit) :=
    (presheafToSheafCompComposeAndSheafifyIso (localizationTopology ℱ)
      AddCommGrpCat.free).app ((Functor.const _).obj PUnit) ≪≫
      Functor.mapIso (presheafToSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
        ((Functor.compConstIso _ AddCommGrpCat.free).symm.app PUnit)
  (Functor.mapIso (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
      addCommGrpFreePUnitIsoZ).symm ≪≫
    e.symm

end Localization

-- Proof sketch: identify the localization at `ℱ` with sheaves on the category of elements of
-- `ℱ`, use the adjunction for `(localizationProjection ℱ).sheafPullback AddCommGrpCat
-- (localizationTopology ℱ) J`, and compare the resulting Hom functor with the free-abelian-sheaf
-- adjunction of Lemma `18.5.2`. Yoneda then yields the canonical isomorphism.
/-- Remark 18.27.10: for a sheaf of sets `ℱ` on `(C, J)`, the lower shriek of the constant
integer sheaf along the localization at `ℱ` is canonically isomorphic to the free abelian sheaf
generated by `ℱ`; this is the statement `j_! \mathbf Z = \mathbf Z_\mathcal F^\#`. -/
noncomputable def localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift.{v} ℤ))) ⟶
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) :=
  (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv
      ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (ULift.{v} ℤ)))
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ)).symm
    ((localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ).hom ≫
      (((Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj).homEquiv
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit)
          (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
              (localizationTopology ℱ) J).obj
            ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ))).symm
        (((localizationConstSingletonToInverseImageEquiv ℱ
            ((sheafForget J).obj ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ))).symm
          ((Sheaf.adjunction J AddCommGrpCat.adj).unit.app ℱ)))))

theorem localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_isIso
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    IsIso (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf ℱ) := by
  sorry

/-- Remark 18.27.10: for a sheaf of sets `ℱ` on `(C, J)`, the lower shriek of the constant
integer sheaf along the localization at `ℱ` is canonically isomorphic to the free abelian sheaf
generated by `ℱ`; this is the statement `j_! \mathbf Z = \mathbf Z_\mathcal F^\#`. -/
noncomputable abbrev localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift.{v} ℤ))) ≅
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) :=
  by
    letI := localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_isIso
      ℱ
    exact asIso
      (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf ℱ)

-- Proof sketch: use the adjunction for
-- `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`, identify
-- morphisms out of the left-hand side with morphisms from `j_! \mathbf Z` into the internal Hom
-- sheaf by the canonical tensor-internal-Hom adjunction
-- `MonoidalClosed.internalHomAdjunction₂`, and conclude by Yoneda exactly as in the textbook
-- argument.
section Monoidal

attribute [local instance] Sheaf.monoidalCategory

/-- For an abelian sheaf `ℋ`, localization followed by lower shriek is canonically identified with
tensoring `ℋ` by the localized constant integer sheaf `j_! \mathbf Z`, where the tensor product is
taken in the chosen sheaf monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`. This is part
`(b)` of the remark in the site-of-elements model of the localization at `ℱ`. -/
private theorem localization_lowerShriek_inverseImage_iso_tensor_constantInteger_nonempty
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [MonoidalCategory AddCommGrpCat.{v}]
    [((J.W : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint]
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    Nonempty
      (((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
          (localizationTopology ℱ) J).obj
          (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
              (localizationTopology ℱ) J).obj ℋ) ≅
        ((((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
            (localizationTopology ℱ) J).obj
            ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
              (AddCommGrpCat.of (ULift.{v} ℤ)))) ⊗ ℋ)) := by
  sorry

/-- For an abelian sheaf `ℋ`, localization followed by lower shriek is canonically identified with
tensoring `ℋ` by the localized constant integer sheaf `j_! \mathbf Z`, where the tensor product is
taken in the chosen sheaf monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`. This is part
`(b)` of the remark in the site-of-elements model of the localization at `ℱ`. -/
noncomputable def localization_lowerShriek_inverseImage_iso_tensor_constantInteger
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [MonoidalCategory AddCommGrpCat.{v}]
    [((J.W : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint]
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
            (localizationTopology ℱ) J).obj ℋ) ≅
      ((((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
          (localizationTopology ℱ) J).obj
          ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
            (AddCommGrpCat.of (ULift.{v} ℤ)))) ⊗ ℋ) :=
  Classical.choice
    (localization_lowerShriek_inverseImage_iso_tensor_constantInteger_nonempty
      ℱ ℋ)

end Monoidal

end CategoryTheory
