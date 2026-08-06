import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

-- Bridge/view item: the core Chapter 19 owner records the suspension axiom as
-- `ReducedCohomologySuspension.suspensionIso` in backward-shift form. This file reindexes that
-- axiom to the forward shift used in Theorem 19.1.4 and its objectwise companion.

local notation "NBasedSpace" => nondegeneratelyBasedSpace

section SuspensionBridge

variable [CategoryWithCofibrations (Under (⊤_ TopCat))]
variable [CategoryWithCofibrations NBasedSpace]
variable (setup : ReducedSuspensionCofiberSetup)
variable (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)

namespace ReducedCohomologySuspension

/-- Reindexing the Chapter 19 suspension axiom gives the forward degree shift
`Ẽ^q(X) ≅ Ẽ^(q + 1)(ΣX)` on the underlying graded functor. -/
theorem forwardShiftIso_nonempty
    [ReducedCohomologySuspension setup E]
    (q : ℤ) :
    Nonempty (E q ≅ setup.suspension.op ⋙ E (q + 1)) := by
  let hSuspension : ReducedCohomologySuspension setup E := inferInstance
  exact Nonempty.map Iso.symm (by simpa using hSuspension.suspensionIso (q + 1))

/-- Applying the forward-shifted suspension isomorphism at `X` yields
`Ẽ^q(X) ≅ Ẽ^(q + 1)(ΣX)`. -/
theorem forwardShiftIsoApp_nonempty
    [ReducedCohomologySuspension setup E]
    (q : ℤ) (X : NBasedSpace) :
    Nonempty ((E q).obj (Opposite.op X) ≅
      (E (q + 1)).obj (Opposite.op (setup.suspension.obj X))) :=
  Nonempty.map (fun e ↦ e.app (Opposite.op X)) (forwardShiftIso_nonempty setup E q)

end ReducedCohomologySuspension

end SuspensionBridge

section ReducedTheory

variable [CategoryWithCofibrations (Under (⊤_ TopCat))]
variable [CategoryWithCofibrations NBasedSpace]
variable [CategoryWithWeakEquivalences NBasedSpace]
variable (setup : ReducedSuspensionCofiberSetup)
variable (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)

/-- Theorem 19.1.4: for a reduced cohomology theory `E` on nondegenerately based spaces,
suspension gives a natural isomorphism `Ẽ^q(X) ≅ Ẽ^(q + 1)(ΣX)`, formalized as the existence of
a natural isomorphism `E q ≅ setup.suspension.op ⋙ E (q + 1)`. -/
theorem reducedCohomologySuspensionNaturalIso
    [ReducedCohomologyTheory setup E]
    (q : ℤ) :
    Nonempty (E q ≅ setup.suspension.op ⋙ E (q + 1)) :=
  ReducedCohomologySuspension.forwardShiftIso_nonempty setup E q

/-- Applying `reducedCohomologySuspensionNaturalIso` at a fixed nondegenerately based space `X`
identifies `Ẽ^q(X)` with `Ẽ^(q + 1)(ΣX)`. -/
theorem reducedCohomologySuspensionNaturalIso_app
    [ReducedCohomologyTheory setup E]
    (q : ℤ) (X : NBasedSpace) :
    Nonempty ((E q).obj (Opposite.op X) ≅
      (E (q + 1)).obj (Opposite.op (setup.suspension.obj X))) :=
  ReducedCohomologySuspension.forwardShiftIsoApp_nonempty setup E q X

end ReducedTheory
