import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap18.Definition_18_43_1
import StacksProject_2024.Chap18.Lemma_18_43_2
import StacksProject_2024.Chap07.Proposition_7_44_3

noncomputable section
universe u v w
namespace CategoryTheory
namespace Sheaf
open CategoryTheory
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable {H : Sheaf J (ModuleCat.{w} Λ)} [IsConstant J H]
example (U : C) : IsConstant (J.over U) (H.over U) := by
  let TU : Over U := Over.mk (𝟙 U)
  let hTU : IsTerminal TU := Over.mkIdTerminal
  have hforget : IsConstant J ((sheafCompose J (forget (ModuleCat.{w} Λ))).obj H) := by
    exact (Sheaf.isConstant_iff_forget (J := J) (U := forget (ModuleCat.{w} Λ)) (F := H) (hT := hTU)).mp inferInstance
  have hsliceforget : IsConstant (J.over U) (((sheafCompose J (forget (ModuleCat.{w} Λ))).obj H).over U) := by
    exact CategoryTheory.isConstant_over_of_isConstant (JC := J) (U := U)
  have hcomp : (((sheafCompose J (forget (ModuleCat.{w} Λ))).obj H).over U) =
      (sheafCompose (J.over U) (forget (ModuleCat.{w} Λ))).obj (H.over U) := rfl
  rw [hcomp] at hsliceforget
  exact (Sheaf.isConstant_iff_forget (J := J.over U) (U := forget (ModuleCat.{w} Λ)) (F := H.over U) (hT := Over.mkIdTerminal)).mpr hsliceforget
