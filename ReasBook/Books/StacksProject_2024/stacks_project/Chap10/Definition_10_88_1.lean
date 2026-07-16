import Mathlib
import StacksProject_2024.stacks_project.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]

/-- Definition 10.88.1: a directed system of `R`-modules is Mittag-Leffler if each stage is
finitely presented and for every `R`-module `N`, the inverse system `i ↦ Hom_R(M_i, N)` is
Mittag-Leffler. -/
def IsMittagLefflerDirectedSystem [Nonempty I] [IsDirectedOrder I] (M : I ⥤ ModuleCat R) : Prop :=
  (∀ i, Module.FinitePresentation R (M.obj i)) ∧
    ∀ N : ModuleCat R,
      (colimitPresentationHomInverseSystem M N).IsMittagLeffler

/-- Unpacking `IsMittagLefflerDirectedSystem` gives the stagewise finite-presentation condition and
the Mittag-Leffler condition on every associated Hom inverse system. -/
theorem isMittagLefflerDirectedSystem_iff [Nonempty I] [IsDirectedOrder I] (M : I ⥤ ModuleCat R) :
    IsMittagLefflerDirectedSystem M ↔
      (∀ i, Module.FinitePresentation R (M.obj i)) ∧
        ∀ N : ModuleCat R,
          (colimitPresentationHomInverseSystem M N).IsMittagLeffler :=
  Iff.rfl

end
