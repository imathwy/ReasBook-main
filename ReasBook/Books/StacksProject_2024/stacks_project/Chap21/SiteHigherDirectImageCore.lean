import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{v}] [HasSheafify JD AddCommGrpCat.{v}]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{v})]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC)]

/-- The `i`-th higher direct image functor on abelian sheaves along a continuous functor of sites.
-/
abbrev higherDirectImageFunctor (i : ℕ) :
    Sheaf JC AddCommGrpCat.{v} ⥤ Sheaf JD AddCommGrpCat.{v} :=
  (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC).rightDerived i

/-- The `i`-th higher direct image of an abelian sheaf along a continuous functor of sites. -/
abbrev higherDirectImage (F : Sheaf JC AddCommGrpCat.{v}) (i : ℕ) :
    Sheaf JD AddCommGrpCat.{v} :=
  (higherDirectImageFunctor u i).obj F

/- Lean surface notation for the higher direct image `R^i u_* F`. A thin macro keeps instance
search at use sites instead of forcing it during notation elaboration. -/
scoped macro:max "R^{" i:term "}_[" u:term "](" F:term ")" : term =>
  `(@higherDirectImage _ _ _ _ _ _ $u _ _ _ _ _ $F $i)

end

end Sheaf
end CategoryTheory
