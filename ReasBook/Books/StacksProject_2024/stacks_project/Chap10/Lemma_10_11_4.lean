import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

-- Source/core/bridge triage:
-- * source-facing: `Module.FinitePresentation R M`
-- * core/canonical: `CategoryTheory.IsFinitelyPresentable (ModuleCat.of R M)`
-- * bridge/view: preservation of filtered colimits by the represented functor `Hom_R(M, -)`
--
-- The owner abstraction is `IsFinitelyPresentable (ModuleCat.of R M)`. The filtered-colimit
-- statement is then obtained by composing with the owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`.

/-- Lemma 10.11.4 (1): an `R`-module is finitely presented if and only if the corresponding object of
`ModuleCat R` is finitely presentable. -/
-- Proof sketch: use the standard equivalence in mathlib between finite presentation of an
-- `R`-module and finite presentability of the associated object of `ModuleCat R`.
theorem module_finitePresentation_iff_isFinitelyPresentable :
    Module.FinitePresentation R M ↔ IsFinitelyPresentable.{v} (ModuleCat.of R M) := sorry

/-- Lemma 10.11.4 (2): an `R`-module is finitely presented if and only if its represented functor
`Hom_R(M, -)` preserves filtered colimits. -/
-- Proof sketch: combine the previous equivalence with the owner-abstraction theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits` for the represented functor.
theorem module_finitePresentation_iff_preservesFilteredColimits_coyoneda :
    Module.FinitePresentation R M ↔
      PreservesFilteredColimits (coyoneda.obj (op (ModuleCat.of R M))) := sorry

end
