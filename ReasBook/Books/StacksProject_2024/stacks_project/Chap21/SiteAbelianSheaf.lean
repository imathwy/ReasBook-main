import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/-- The category of sheaves of abelian groups on a Grothendieck site. -/
abbrev SiteAbelianSheafCat (J : GrothendieckTopology C) :=
  Sheaf J AddCommGrpCat.{max u v}

/-- Sheaves of abelian groups on a site form an abelian category. -/
instance sheafAddCommGrpCat_abelian (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}] :
    Abelian (SiteAbelianSheafCat J) :=
  sheafIsAbelian

end

end CategoryTheory
