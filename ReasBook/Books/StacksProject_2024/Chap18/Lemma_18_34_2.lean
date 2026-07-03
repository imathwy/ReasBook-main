import Mathlib
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

noncomputable section

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}}
variable {E F G : ringedSiteModuleCategory J O₂}

-- Proof sketch: evaluate at each object of the site and apply the usual composition result for
-- objectwise differential operators, whose orders add under composition.
/-- Lemma 18.34.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `O₂`-modules is a differential operator of order `k + k'`. -/
theorem isDifferentialOperatorOfOrder_comp
    (φ : O₁ ⟶ O₂)
    {k k' : ℕ}
    {D : (restrictionAlong φ).obj E ⟶ (restrictionAlong φ).obj F}
    {D' : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k)
    (hD' : IsDifferentialOperatorOfOrder φ D' k') :
    IsDifferentialOperatorOfOrder φ (D ≫ D') (k + k') := sorry

end SheafOfModules.RingedSite
