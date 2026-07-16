import StacksProject_2024.stacks_project.Chap34.Lemma_34_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed `Scheme.OpenCover` as the canonical Zariski-cover
-- owner; local Chapter 34 fixes `PhCovering` as the source-facing owner for ph coverings.

/-- Lemma 34.8.5: a Zariski covering is a ph covering. -/
@[stacks 0DBH]
theorem phCovering_of_zariskiCovering {T : Scheme.{u}} (cover : T.OpenCover) :
    PhCovering (fun i : cover.I₀ ↦ cover.X i) (fun i ↦ cover.f i) := sorry

end AlgebraicGeometry
