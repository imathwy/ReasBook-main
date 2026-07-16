import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_8_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` did not surface a direct scheme-level equivalence for this
-- Stacks item. Local Chapter 28/31 precedent fixes the owners as the Cohen-Macaulay affine-local
-- condition from `Definition_28_8_1`, `X.embeddedPoints = (∅ : Set X)`, and the scheme-level
-- dimension bound `topologicalKrullDim X ≤ 1`.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 31.4.4: let `X` be a locally Noetherian scheme of dimension `≤ 1`. The following are
equivalent: `X` is Cohen-Macaulay, and `X` has no embedded points. The dimension hypothesis is
formalized as `topologicalKrullDim X ≤ 1`, and the no-embedded-points clause as
`X.embeddedPoints = (∅ : Set X)`. -/
@[stacks 0BXG]
theorem cohenMacaulay_iff_embeddedPoints_eq_empty_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X ≤ 1) :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      X.embeddedPoints = (∅ : Set X) := sorry

end AlgebraicGeometry.Scheme
