import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open TopologicalSpace

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` only surfaced general locally Noetherian scheme API; local
-- Chapter 29/31 precedent fixes the source-facing owners as `schemeTheoreticallyDense`,
-- `X.embeddedPoints`, and `X.associatedPoints`.

/-- Lemma 31.4.5: let `X` be a locally Noetherian scheme and let `U ⊆ X` be an open subscheme.
The following are equivalent: `U` is scheme theoretically dense in `X`; `U` is dense in `X` and
contains all embedded points of `X`; and `U` contains all associated points of `X`. -/
@[stacks 083P]
theorem schemeTheoreticallyDense_open_tfae_dense_embeddedPoints_associatedPoints
    (U : X.Opens) :
    List.TFAE [
      schemeTheoreticallyDense U,
      Dense (U : Set X) ∧ X.embeddedPoints ⊆ (U : Set X),
      X.associatedPoints ⊆ (U : Set X)
    ] := sorry

end AlgebraicGeometry.Scheme
