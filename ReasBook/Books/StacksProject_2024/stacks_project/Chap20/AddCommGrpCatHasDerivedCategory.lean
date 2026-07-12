import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian

open CategoryTheory

noncomputable section

universe u

/-- The standard derived-category structure on `AddCommGrpCat`. -/
instance addCommGrpCat_hasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}
