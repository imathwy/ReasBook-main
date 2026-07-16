import Mathlib
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Lightweight owner API extracted from Lemma 29.11.5 so later local results can reuse the
-- quasi-coherent algebra-over-a-scheme interface without importing the heavier equivalence file.

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u})

local notation "J" => Opens.grothendieckTopology S

private abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

/-- The object property on `Under S.sheaf` cutting out quasi-coherent `\mathcal O_S`-algebras. -/
abbrev qcAlgebraUnderProperty (S : Scheme.{u}) : ObjectProperty (Under (schemeCommRingSheaf S)) :=
  fun A ↦
    ((restrictionAlong A.hom).obj
      (unitModule (Opens.grothendieckTopology S)
        (show CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} from
          A.right))).IsQuasicoherent

/-- The category of quasi-coherent sheaves of `\mathcal O_S`-algebras on `S`. -/
abbrev QcAlgebraUnder (S : Scheme.{u}) :=
  (qcAlgebraUnderProperty S).FullSubcategory

namespace QcAlgebraUnder

/-- The forgetful functor from quasi-coherent `\mathcal O_S`-algebras to all
`\mathcal O_S`-algebras. -/
abbrev forget (S : Scheme.{u}) : S.QcAlgebraUnder ⥤ Under (schemeCommRingSheaf S) :=
  (qcAlgebraUnderProperty S).ι

/-- An object of `S.QcAlgebraUnder` has quasi-coherent underlying `\mathcal O_S`-module after
restricting the target unit module along the algebra structure map. -/
theorem isQuasicoherent_restrictedUnit (A : S.QcAlgebraUnder) :
    ((restrictionAlong A.obj.hom).obj
      (unitModule (Opens.grothendieckTopology S)
        (A.obj.right : CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}))).IsQuasicoherent :=
  A.property

end QcAlgebraUnder

end Scheme
end AlgebraicGeometry
