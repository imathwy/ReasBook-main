import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- - `lean_leansearch` recalled the canonical scheme-morphism owners
--   `LocallyOfFiniteType`, `LocallyOfFinitePresentation`, and the ring-level bridge
--   `RingHom.FinitePresentation.of_finiteType`;
-- - local Chapter 29 precedent records source-side “of finite type” and “of finite presentation”
--   through `Scheme.Hom.FiniteType` and `Scheme.Hom.FinitePresentation`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.21.9 (1): if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite type,
then `f` is locally of finite presentation. -/
@[stacks 01TX]
theorem locallyOfFinitePresentation_of_locallyOfFiniteType [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.21.9 (2): if `S` is locally Noetherian and `f : X ⟶ S` is of finite type, then `f`
is of finite presentation. -/
@[stacks 01TX]
theorem finitePresentation_of_finiteType [FiniteType f] [AlgebraicGeometry.IsLocallyNoetherian S] :
    FinitePresentation f := sorry

end AlgebraicGeometry.Scheme.Hom
