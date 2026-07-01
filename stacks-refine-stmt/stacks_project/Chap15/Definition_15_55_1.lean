import Mathlib.Algebra.Category.ModuleCat.Injective
import stacks_project.Chap12.Lemma_12_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ModuleCat

universe u v

section

variable (R : Type u) [Ring R] (J : Type v) [AddCommGroup J] [Module R J]

namespace Module

-- Domain-style sampling:
-- * primary domain: injective objects in the abelian category `ModuleCat R`, expressed through the
--   represented contravariant Hom functor `preadditiveYonedaObj`.
-- * inspected owner declarations: `CategoryTheory.injective_iff_exact_preadditiveYonedaObj`,
--   `Module.injective_iff_injective_object`, and the underlying mathlib criterion
--   `injective_of_preservesFiniteColimits_preadditiveYonedaObj`.
-- * best owner abstraction: categorical injectivity of `of R J`.
-- * layer: `bridge/view`; the source item is the module-level reformulation of the Chapter 12
--   owner theorem.
-- * primitive data: only the `R`-module `J`.
-- * derived API: exactness of `preadditiveYonedaObj (of R J)`.

/-- Definition 15.55.1: an `R`-module `J` is injective if and only if the contravariant Hom
functor `Hom_R(-, J)`, formalized as `preadditiveYonedaObj (of R J)`, is exact. -/
theorem injective_iff_exact_preadditiveYonedaObj :
    Module.Injective R J ↔
      exactFunctor (ModuleCat R)ᵒᵖ _ (preadditiveYonedaObj (of R J)) := by
  letI := CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  simpa [Module.injective_iff_injective_object R J] using
    (CategoryTheory.injective_iff_exact_preadditiveYonedaObj (of R J))

end Module

end
