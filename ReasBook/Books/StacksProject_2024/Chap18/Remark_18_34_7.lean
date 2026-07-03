import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksProject_2024.Chap18.Lemma_18_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A B B' : Sheaf J CommRingCat.{u}} (β : B ⟶ B')

/-- A `B'`-module sheaf viewed as a `B`-module sheaf by restriction of scalars along `β`. -/
abbrev principalPartsBaseChangeTarget
    (F' : ringedSiteModuleCategory J B') :
    ringedSiteModuleCategory J B :=
  (restrictionAlong β).obj F'

variable (φ : A ⟶ B)
variable {F : ringedSiteModuleCategory J B}

-- Proof sketch: this is the representing property of the chosen order-`k` principal-parts sheaf
-- `P`. Once the differential operator `D` to the restricted target principal-parts sheaf is
-- available from the change-of-rings data, apply the factorization theorem of
-- `principalPartsDifferentialOperator hP` to obtain the unique `B`-linear morphism `P ⟶ P'`.
/-- Remark 18.34.7: for a morphism `A ⟶ B` of sheaves of commutative rings on a site, a chosen
order-`k` principal-parts sheaf `P^k_{B/A}(F)` of a `B`-module sheaf `F`, and any order-`k`
differential operator from `F` to the restriction of a target principal-parts sheaf along a map
`B ⟶ B'`, there is a unique induced map from `P^k_{B/A}(F)` to that restricted target sheaf. This
is the universal-property core of the base-change system of principal-parts maps described in the
remark. -/
theorem principalPartsBaseChange_existsUnique
    (k : ℕ) {P : ringedSiteModuleCategory J B}
    {P' : ringedSiteModuleCategory J B'}
    (hP : (differentialOperatorsFunctor φ F k).CorepresentableBy P)
    (D : (restrictionAlong φ).obj F ⟶
      (restrictionAlong φ).obj (principalPartsBaseChangeTarget β P'))
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    ∃! τ : P ⟶ principalPartsBaseChangeTarget β P',
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ = D := sorry

end
