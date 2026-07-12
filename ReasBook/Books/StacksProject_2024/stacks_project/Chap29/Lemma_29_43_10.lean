import StacksProject_2024.Chap29.Definition_29_40_1
import StacksProject_2024.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced general scheme-morphism owners such as `QuasiCompact`,
-- `LocallyOfFiniteType`, and `IsProper`, but no upstream theorem for this exact implication.
-- Local Chapter 29 precedent provides the source-facing owners `Projective` and
-- `QuasiProjective`. The Stacks tag evidence is consistent: item tag `07RL` matches the source
-- URL `/tag/07RL`.

/-- Lemma 29.43.10: A projective morphism is quasi-projective. -/
@[stacks 07RL]
theorem Projective.toQuasiProjective (hf : Projective f) :
    QuasiProjective f := sorry

end AlgebraicGeometry
