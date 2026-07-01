import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})

/- Lemma 18.12.2: for a morphism of topoi presented by a continuous functor `F : D ⥤ C`,
the inverse image of a sheaf of `𝒪`-modules on `D` is the canonical pullback functor on
sheaves of modules along the unit map `𝒪 ⟶ f_* f^{-1} 𝒪`. Its values are sheaves of modules over
the pulled-back ring `f^{-1} 𝒪`, so the construction is functorial in `\mathcal G`. -/
#check
  (SheafOfModules.pullback
    ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪) :
      SheafOfModules 𝒪 ⥤ _)
