import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Construction_4_5_5

open TopCat
open scoped ContinuousMap

universe u

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` and
-- `ContractibleSpace` are the canonical owners for the homotopy-equivalence and
-- contractibility clauses in this cone-adjunction cover.

noncomputable section

variable {B : Type u} [TopologicalSpace B]

namespace ConnectedCoveringSpace

/-- Lemma 4.5.6 (1): for the covering map `Hom.hom X.obj.hom`, the subset
`U = coneAdjunctionSetU (Hom.hom X.obj.hom)`, corresponding to
`B ∪ (X.obj.left × [0, 3 / 4))` inside `B ∪_{X.obj.hom} CE`, is open. -/
theorem coneAdjunctionSetU_isOpen (X : ConnectedCoveringSpace B) :
    IsOpen X.coneAdjunctionSetU := sorry

/-- Lemma 4.5.6 (2): for the covering map `Hom.hom X.obj.hom`, the subset
`V = coneAdjunctionSetV (Hom.hom X.obj.hom)`, corresponding to
`X.obj.left × (1 / 4, 1]` inside `B ∪_{X.obj.hom} CE`, is open. -/
theorem coneAdjunctionSetV_isOpen (X : ConnectedCoveringSpace B) :
    IsOpen X.coneAdjunctionSetV := sorry

/-- Lemma 4.5.6 (3): for the covering map `Hom.hom X.obj.hom`, the open set
`U = coneAdjunctionSetU (Hom.hom X.obj.hom)` is homotopy equivalent to `B`. -/
theorem coneAdjunctionSetU_exists_homotopyEquiv_base (X : ConnectedCoveringSpace B) :
    ∃ e : X.coneAdjunctionSetU ≃ₕ B, e.invFun = X.coneAdjunctionSetUBaseMap := sorry

/-- Lemma 4.5.6 (4): for the covering map `Hom.hom X.obj.hom`, the overlap
`U ∩ V = coneAdjunctionSetUInterV (Hom.hom X.obj.hom)` is homotopy equivalent to
`X.obj.left`. -/
theorem coneAdjunctionSetUInterV_exists_homotopyEquiv_source (X : ConnectedCoveringSpace B) :
    ∃ e : X.coneAdjunctionSetUInterV ≃ₕ X.obj.left,
      e.invFun = X.coneAdjunctionSetUInterVMidpointMap := sorry

/-- Lemma 4.5.6 (5): for the covering map `Hom.hom X.obj.hom`, the open set
`V = coneAdjunctionSetV (Hom.hom X.obj.hom)` is contractible. -/
instance coneAdjunctionSetV_contractible (X : ConnectedCoveringSpace B) :
    ContractibleSpace X.coneAdjunctionSetV := sorry

end ConnectedCoveringSpace

end
