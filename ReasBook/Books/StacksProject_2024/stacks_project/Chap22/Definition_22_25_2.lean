import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.stacks_project.Chap22.Definition_22_25_1

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u u' u''

namespace CategoryTheory

section

open scoped GradedCategory

variable {R : Type w} [Semiring R]
variable {C : Type u} {D : Type u'} {E : Type u''}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable [Preadditive C] [Preadditive D] [Preadditive E]
variable [gradedC : GradedCategory R C] [gradedD : GradedCategory R D] [gradedE : GradedCategory R E]

namespace Functor

/-- Definition 22.25.2: a functor of graded categories over `R`, or a graded functor, is an
additive `R`-linear functor that preserves the degree of every homogeneous morphism. -/
@[stacks 09L3]
class Graded (R : Type w) [Semiring R] [gradedC : GradedCategory R C]
    [gradedD : GradedCategory R D]
    (F : C ⥤ D) : Prop extends F.Additive, Functor.Linear R F where
  /-- A graded functor sends degree-`i` morphisms to degree-`i` morphisms. -/
  map_mem_homDegree {X Y : C} (i : ℤ) {f : X ⟶ Y}
      (hf : f ∈ (Hom^i(X, Y) : Submodule R (X ⟶ Y))) :
      F.map f ∈ (Hom^i(F.obj X, F.obj Y) : Submodule R (F.obj X ⟶ F.obj Y))

section

variable {F : C ⥤ D} [Graded R F]

/-- A graded functor sends degree-`i` morphisms to degree-`i` morphisms. -/
theorem map_mem_homDegree {X Y : C} (i : ℤ) {f : X ⟶ Y}
    (hf : f ∈ (Hom^i(X, Y) : Submodule R (X ⟶ Y))) :
    F.map f ∈ (Hom^i(F.obj X, F.obj Y) : Submodule R (F.obj X ⟶ F.obj Y)) :=
  (inferInstance : Graded R F).map_mem_homDegree i hf

end

/-- The identity functor on a graded category is a graded functor. -/
instance instGradedId : Graded R (𝟭 C) where
  map_mem_homDegree {X} {Y} i {f} hf := by
    simpa using hf

/-- The composite of graded functors is a graded functor. -/
instance instGradedComp (F : C ⥤ D) (G : D ⥤ E) [hF : Graded R F] [hG : Graded R G] :
    Graded R (F ⋙ G) where
  map_mem_homDegree {X} {Y} i {f} hf := by
    exact G.map_mem_homDegree i <| F.map_mem_homDegree i hf

end Functor

end

end CategoryTheory
