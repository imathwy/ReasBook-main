import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

universe v u

section

variable {R : Type u} [Ring R] [Small.{v} R]
variable (P : Type v) [AddCommGroup P] [Module R P]

-- Domain-style sampling:
-- * primary domain: projective objects in the abelian category `ModuleCat R`, detected through
--   `Projective`, `preadditiveCoyonedaObj`, and `exactFunctor`.
-- * inspected owner declarations: `IsProjective.iff_projective`,
--   `preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`,
--   `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`, and `exactFunctor_iff`.
-- * best owner abstraction: categorical projectivity of `of R P`.
-- * layer: `bridge/view`; the source item is a module-theoretic reformulation of the owner
--   projectivity predicate in terms of the represented Hom functor.
-- * primitive data: only the `R`-module `P`.
-- * derived API: exactness of `preadditiveCoyonedaObj (of R P)` and the comparison theorem
--   `IsProjective.iff_projective`.
/-- Definition 10.77.1: an `R`-module `P` is projective if and only if the represented Hom
functor `Hom_R(P, -)` is exact. In Lean this exact functor is
`preadditiveCoyonedaObj (of R P)`, whose codomain is the module category over the
opposite endomorphism ring of `P`. -/
@[stacks 05CE]
theorem module_projective_iff_exact_hom_functor :
    Module.Projective R P ↔
      exactFunctor (ModuleCat R) _ (preadditiveCoyonedaObj (of R P)) := by
  constructor
  · intro hP
    letI : Projective (of R P) := (IsProjective.iff_projective P).1 hP
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj (of R P)) :=
      preservesFiniteColimits_preadditiveCoyonedaObj_of_projective (of R P)
    rw [exactFunctor_iff]
    constructor <;> infer_instance
  · intro hExact
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj (of R P)) :=
      (exactFunctor_iff (preadditiveCoyonedaObj (of R P))).1 hExact |>.2
    letI : Projective (of R P) :=
      projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (of R P)
    exact (IsProjective.iff_projective P).2 inferInstance

end
