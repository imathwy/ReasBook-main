import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced the canonical properness owner
-- `AlgebraicGeometry.IsProper`; local Chapter 29 precedent provides the source-facing
-- `AlgebraicGeometry.LocallyProjective` owner in `Definition_29_43_1`.

/-- Lemma 29.43.5: A locally projective morphism is proper. -/
@[stacks 01WC]
theorem LocallyProjective.isProper [LocallyProjective f] :
    IsProper f := sorry

end AlgebraicGeometry
