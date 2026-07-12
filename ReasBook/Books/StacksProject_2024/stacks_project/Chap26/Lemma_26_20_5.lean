import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

-- Semantic recall: `lean_leansearch` surfaced the exact canonical owner theorem
-- `AlgebraicGeometry.ValuativeCriterion.Existence.eq`, identifying the existence part of the
-- valuative criterion with the universally-specializing morphism property.

/- Lemma 26.20.5: for a morphism of schemes `f : X ⟶ S`, specializations lift along every
base change of `f` if and only if `f` satisfies the existence part of the valuative criterion.
This is the canonical equality of morphism properties `ValuativeCriterion.Existence.eq`. -/
recall AlgebraicGeometry.ValuativeCriterion.Existence.eq

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

#check (ValuativeCriterion.Existence.eq :
    ValuativeCriterion.Existence = (topologically @SpecializingMap).universally)

end
