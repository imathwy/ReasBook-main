import Mathlib
import StacksProject_2024.Chap10.Lemma_10_78_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of modules over a commutative ring;
- sampled owner-style declarations of the same kind:
  `Module.Projective`,
  `Module.FinitePresentation`,
  `Module.Flat.projective_of_finitePresentation`,
  `module_finite_projective_tfae`;
- owner abstraction: the owner predicates `Module.Finite R M` and `Module.Projective R M`;
- primitive data: the ring `R` and the module `M`;
- derived API: the equivalent finitely presented flat formulation.

This numbered item is `source-facing`, but it adds no extra mathematical structure beyond the owner
predicates already used in the chapter. The refinement therefore deletes the parallel local wrapper
abbreviations and states the equivalence directly on the owner predicates, derived from the chapter
owner theorem `module_finite_projective_tfae`.
-/

-- Proof sketch: for the forward implication, a finite projective module is finitely presented by
-- `Module.finitePresentation_of_projective` and flat by `Module.Flat.of_projective`. For the
-- reverse implication, a finitely presented flat module is projective by
-- `Module.Flat.projective_of_finitePresentation`, and finite presentation already implies
-- finiteness.
/-- Lemma 10.83.1: an `R`-module `M` is finite projective if and only if it is finitely presented
and flat. -/
theorem module_finite_projective_iff_finitePresentation_and_flat :
    (Module.Finite R M ∧ Module.Projective R M) ↔
      Module.FinitePresentation R M ∧ Module.Flat R M := by
  simpa using module_finite_projective_tfae.out 1 0

end
