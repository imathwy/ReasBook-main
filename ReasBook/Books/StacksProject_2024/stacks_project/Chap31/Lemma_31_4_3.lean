import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Definition_31_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` did not return a useful direct sheaf-level analogue for this
-- equivalence. Local Chapter 10/30/31 precedent fixes the source-facing owners as
-- `embeddedAssociatedPoints ℱ` and `satisfiesSerreConditionS ℱ 1`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 31.4.3: let `X` be a locally Noetherian scheme and let `\mathcal F` be a coherent
sheaf on `X`. Then `\mathcal F` has no embedded associated points if and only if it satisfies
Serre's condition `(S_1)`. -/
@[stacks 0346]
theorem embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ℱ.embeddedAssociatedPoints = (∅ : Set X) ↔ satisfiesSerreConditionS ℱ 1 := sorry

/-- Lemma 31.4.3 in the forward direction: if `\mathcal F` has no embedded associated points,
then it satisfies Serre's condition `(S_1)`. -/
theorem satisfiesSerreConditionS_one_of_embeddedAssociatedPoints_eq_empty
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (h_empty : ℱ.embeddedAssociatedPoints = (∅ : Set X)) :
    satisfiesSerreConditionS ℱ 1 :=
  (embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one ℱ).mp h_empty

/-- Lemma 31.4.3 in the reverse direction: an `(S_1)` coherent sheaf has no embedded associated
points. -/
theorem embeddedAssociatedPoints_eq_empty_of_satisfiesSerreConditionS_one
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hS1 : satisfiesSerreConditionS ℱ 1) :
    ℱ.embeddedAssociatedPoints = (∅ : Set X) :=
  (embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one ℱ).mpr hS1

end AlgebraicGeometry.Scheme.Modules
