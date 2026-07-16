import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Functors
import StacksProject_2024.stacks_project.Chap12.Definition_12_31_2

open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- The degree-`p` site cohomology functor on sheaves of `A`-modules, computed on the underlying
abelian sheaves. -/
abbrev siteModuleCohomologyFunctor (p : ℕ) :
    Sheaf J (ModuleCat A) ⥤ AddCommGrpCat.{max u v w} :=
  sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat) ⋙ Sheaf.cohomologyFunctor J p

/-- The sequential inverse system `n ↦ H^p(\mathcal C, \mathcal F_n)` attached to a sequential
inverse system of sheaves of `A`-modules on `(C, J)`. -/
abbrev siteModuleCohomologyTower
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ) :
    SequentialInverseSystem AddCommGrpCat.{max u v w} :=
  ℱ ⋙ siteModuleCohomologyFunctor p

end CategoryTheory
