import Mathlib
import StacksProject_2024.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Semantic recall: `lean_leansearch` identified `AlgebraicGeometry.UniversallyOpen` as the
-- canonical scheme-morphism owner for universal openness; local Chapter 29 precedent records
-- syntomic morphisms by the source-facing owner `Syntomic f`.

/-- Lemma 29.30.8: a syntomic morphism is universally open. -/
@[stacks 056F]
theorem universallyOpen_of_syntomic (hf : Syntomic f) :
    UniversallyOpen f := sorry

end AlgebraicGeometry
