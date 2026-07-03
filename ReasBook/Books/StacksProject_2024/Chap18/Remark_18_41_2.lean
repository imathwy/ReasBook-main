import Mathlib
import stacks_project.Chap18.Lemma_18_41_1
import stacks_project.Chap18.«18_41_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (JD.over (u.obj U)) AddCommGrpCat.{u}]
variable [∀ U : C, ∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.post u).op.HasLeftKanExtension F]
variable (𝒪D : Sheaf JD CommRingCat.{u})

/-- The inverse-image structure sheaf `g^{-1} \mathcal O_\mathcal D`, viewed as a
`RingCat`-valued sheaf on `\mathcal C`. -/
abbrev inverseImageRingSheaf : Sheaf JC RingCat.{u} :=
  (u.sheafPushforwardContinuous RingCat.{u} JC JD).obj (ringSheaf JD 𝒪D)

/-- The inverse-image functor on `\mathcal O_\mathcal D`-modules induced by the identity map on
`g^{-1}\mathcal O_\mathcal D`. -/
abbrev moduleInverseImage :
    SheafOfModules (ringSheaf JD 𝒪D) ⥤
      SheafOfModules
        ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
          (ringSheaf JD 𝒪D)) :=
  SheafOfModules.pushforward
    (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
      (ringSheaf JD 𝒪D)))

/-- The chosen lower shriek `g_! : \mathrm{Mod}(g^{-1}\mathcal O_\mathcal D) \to
\mathrm{Mod}(\mathcal O_\mathcal D)`, defined as the left adjoint of the inverse-image functor on
modules from Lemma `18.41.1`. -/
abbrev moduleLowerShriek :
    SheafOfModules
      ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        (ringSheaf JD 𝒪D)) ⥤
      SheafOfModules (ringSheaf JD 𝒪D) :=
  Functor.leftAdjoint (moduleInverseImage u 𝒪D)

/-- The localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1`, viewed in the fixed setup of
this remark. -/
abbrev localizedComparisonOnStructureSheaves (U : C) :
    ((Over.post u).sheafPullback AddCommGrpCat.{u}
        (JC.over U) (JD.over (u.obj U))).obj
      (CategoryTheory.localizedStructureAbelianSheaf JC
        ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
    CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U) :=
  CategoryTheory.compare_on_localizations u 𝒪D U

/-- The local criterion from `18.41.2.1`: every slice-site comparison
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` is an isomorphism. -/
abbrev localizedComparisonMapsAreIso : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves u 𝒪D U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (CategoryTheory.localizedStructureAbelianSheaf JC
            ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
        CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))

/-- The fixed-context local hypothesis that all comparison maps from `18.41.2.1` are
isomorphisms. -/
abbrev localizedComparisonCondition : Prop :=
  ∀ U : C,
    IsIso
      ((localizedComparisonOnStructureSheaves u 𝒪D U) :
        ((Over.post u).sheafPullback AddCommGrpCat.{u}
            (JC.over U) (JD.over (u.obj U))).obj
          (CategoryTheory.localizedStructureAbelianSheaf JC
            ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
        CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))

-- Proof sketch: the proof of Lemma `18.41.1` constructs the comparison from abelian lower shriek
-- followed by forgetfulness to forgetting after module lower shriek by checking the generating
-- modules `j_{U!}\mathcal O_U`. If each localized comparison map
-- `compare_on_localizations u 𝒪D U` is an isomorphism, then the comparison is an isomorphism on
-- those generators, hence the induced transformation of functors is a natural isomorphism.
/-- Remark 18.41.2: in general the square formed by lower shriek on modules, lower shriek on
underlying abelian sheaves, and the forgetful functors need not commute. However, if for every
object `U` of `\mathcal C` the localized comparison morphism
`(g')^{Ab}_! \mathcal O_U \to \mathcal O_{u(U)}` from `18.41.2.1` is an isomorphism, then the
comparison between `g^{Ab}_! ∘ forget` and `forget ∘ g_!` is a natural isomorphism. -/
theorem lowerShriek_toSheaf_comparison_exists_of_compare_on_localizations
    (hlocal :
      ∀ U : C,
        IsIso
          ((localizedComparisonOnStructureSheaves u 𝒪D U) :
            ((Over.post u).sheafPullback AddCommGrpCat.{u}
                (JC.over U) (JD.over (u.obj U))).obj
              (CategoryTheory.localizedStructureAbelianSheaf JC
                ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) U) ⟶
            CategoryTheory.localizedStructureAbelianSheaf JD 𝒪D (u.obj U))) :
    ∃ comparison :
      SheafOfModules.toSheaf
        ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj
          (ringSheaf JD 𝒪D)) ⋙
        u.sheafPullback AddCommGrpCat.{u} JC JD ⟶
        moduleLowerShriek u 𝒪D ⋙
          SheafOfModules.toSheaf (ringSheaf JD 𝒪D),
      ∀ ℱ, IsIso (comparison.app ℱ) := sorry

end

end SheafOfModules
