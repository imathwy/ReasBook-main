import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-- The localized structure module `\mathcal O_U` on the slice site `(C/U, J.over U)`, extended
by zero to a sheaf of `\mathcal O`-modules on `(C, J)`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (SheafOfModules.pullback
      (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))).obj
    (SheafOfModules.unit
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

namespace LocalizedStructureModuleExtensionByZero

set_option quotPrecheck false in
scoped notation:max "j![" 𝒪:max ", " U:max "]" =>
  SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero _ 𝒪 U

end LocalizedStructureModuleExtensionByZero

open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

private noncomputable def localizedSectionsEquivEvaluation
    (ℱ : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) ↦ by
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Evaluating `localizedSectionsEquivEvaluation` on a section produced by `unitHomEquiv`
recovers the terminal component of the corresponding unit morphism on the slice over `U`. -/
private theorem localizedSectionsEquivEvaluation_unitHomEquiv
    (ℱ : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (φ :
      SheafOfModules.unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U) ⟶
        SheafOfModules.over ℱ U) :
    localizedSectionsEquivEvaluation J 𝒪 U ℱ ((SheafOfModules.over ℱ U).unitHomEquiv φ) =
      (φ.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)).val.obj
            (op (Over.mk (𝟙 U)))) from
          (1 : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).1.obj (op U))) := by
  rfl

/-- 18.19.2.1: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, and an
`\mathcal O`-module sheaf `\mathcal F`, there is a canonical bijection
`Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)`. -/
noncomputable def localizedStructureModuleExtensionByZero_homEquiv
    (ℱ : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    (localizedStructureModuleExtensionByZero J 𝒪 U ⟶ ℱ) ≃
    (SheafOfModules.evaluation
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) (op U)).obj ℱ :=
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))).homEquiv
      (SheafOfModules.unit
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)) ℱ).trans
    (SheafOfModules.over ℱ U).unitHomEquiv).trans
    (localizedSectionsEquivEvaluation J 𝒪 U ℱ)

omit [HasBinaryProducts C] in
/-- Postcomposition on the `Hom` side of `localizedStructureModuleExtensionByZero_homEquiv`
matches the induced restriction map on sections. -/
@[simp] theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)}
    (β : localizedStructureModuleExtensionByZero J 𝒪 U ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  simp only [localizedStructureModuleExtensionByZero_homEquiv, Equiv.trans_apply]
  rw [localizedSectionsEquivEvaluation_unitHomEquiv,
    localizedSectionsEquivEvaluation_unitHomEquiv]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The canonical morphism `j_{V!}\mathcal O_V ⟶ j_{U!}\mathcal O_U` attached to a map
`f : V ⟶ U`, obtained by transporting the restriction of the universal section of
`j_{U!}\mathcal O_U` along the owner equivalence
`Hom_{\mathcal O}(j_{V!}\mathcal O_V, -) ≃ (-)(V)`. -/
noncomputable def localizedStructureModuleExtensionByZeroMap
    {V U : C} (f : V ⟶ U) :
    j![𝒪, V] ⟶ j![𝒪, U] :=
  (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V (j![𝒪, U])).symm
    (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj (j![𝒪, U])).1.map f.op
      ((localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U (j![𝒪, U])) (𝟙 _)))

end SheafOfModules.RingedSite
