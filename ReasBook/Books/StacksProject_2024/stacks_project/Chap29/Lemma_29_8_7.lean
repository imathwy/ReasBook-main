import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `isDominant_iff_forall_genericPointOfComponent_mem_range` in `Lemma_29_8_3` is the Chapter 29
--   canonical owner for the generic-point criterion for dominance.
-- - The source-facing new content here is the finite-source version of that generic-point
--   criterion, together with its finiteness consequence for `irreducibleComponents S`.
-- - Nearby Chapter 29 files already use `Finite (irreducibleComponents X)` as the canonical
--   finiteness owner for the irreducible-component space of a scheme.
-- - The Stacks tag evidence is consistent: item tag `01RM` matches the source URL `/tag/01RM`.

/- Lemma 29.8.7: if `f : X ⟶ S` is a morphism of schemes and `X` has finitely many irreducible
components, then `f` is dominant if and only if the generic point of every irreducible component
of `S` lies in the image of `f`. -/
@[stacks 01RM]
theorem isDominant_iff_forall_genericPointOfComponent_mem_range_of_finite_irreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] :
    IsDominant f ↔
      ∀ Z : irreducibleComponents S, ((genericPoints.ofComponent Z : S) ∈ Set.range f.base) := sorry

/-- Lemma 29.8.7 (2): if `f : X ⟶ S` is a dominant morphism of schemes and `X` has finitely many
irreducible components, then `S` has finitely many irreducible components. -/
@[stacks 01RM]
theorem finite_irreducibleComponents_target_of_isDominant
    {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] [IsDominant f] :
    Finite (irreducibleComponents S) := sorry

end AlgebraicGeometry
