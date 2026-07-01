import Mathlib
import stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]

local instance (M : ModuleCat.{v} (DualNumber R)) : Module R M :=
  Module.compHom M (algebraMap R (DualNumber R))

/- Source/core/bridge triage:
* source-facing: existence of a dual-number counterexample to ascent for the Mittag-Leffler
  property.
* core/canonical: the chapter owner `Module.MittagLeffler` on the underlying module carrier of a
  bundled `ModuleCat`.
* bridge/view: the induced `R`-module structure on a `DualNumber R`-module via restriction of
  scalars along `algebraMap R (DualNumber R)`.
-/
-- Proof sketch: start from a non-Mittag-Leffler `R`-module `M₀` and choose a presentation by free
-- modules `F₁ ⟶ F₀ ⟶ M₀ ⟶ 0`. Endow `F₁ ⊕ F₀` with the dual-number action coming from the square-zero
-- endomorphism given by the presentation map. As an `R`-module this object is free, hence
-- Mittag-Leffler over `R`; if it were Mittag-Leffler over `DualNumber R`, then reduction modulo
-- `ε` would also be Mittag-Leffler, forcing `F₁ ⊕ M₀` to be Mittag-Leffler over `R`, a
-- contradiction.
/-- Remark 10.88.13: assuming there exists an `R`-module which is not Mittag-Leffler, the dual
numbers over `R` provide a counterexample to ascent of the Mittag-Leffler property: there exists a
`DualNumber R`-module which is Mittag-Leffler when viewed as an `R`-module, but which is not
Mittag-Leffler as a `DualNumber R`-module. -/
theorem exists_dualNumber_module_mittagLeffler_over_base_not_over_dualNumber
    (h₀ : ∃ M₀ : ModuleCat.{v} R, ¬ MittagLeffler R M₀) :
    ∃ M : ModuleCat.{v} (DualNumber R),
      MittagLeffler R M ∧ ¬ MittagLeffler (DualNumber R) M := sorry

end

end Module
