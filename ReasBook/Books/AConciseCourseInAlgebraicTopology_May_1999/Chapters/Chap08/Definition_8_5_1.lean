import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

open CategoryTheory

noncomputable section

/-- The singleton subset consisting of the chosen basepoint of a based space. -/
abbrev basedBasepointSet (A : BasedSpace) : Set A.right :=
  {underTopBasepoint A}

/-- Relative homotopies of maps out of a based space, fixed at its chosen basepoint. -/
abbrev BasedHomotopyRel {A B : BasedSpace} (f g : C(A.right, B.right)) : Type _ :=
  ContinuousMap.HomotopyRel f g (basedBasepointSet A)

notation:50 f " HRel[" A "] " g => ContinuousMap.HomotopyRel f g (basedBasepointSet A)

-- Semantic recall: `lean_leansearch` surfaced covering-space lifting results and model-category
-- fibrations, but no canonical topological owner for pointed fibrations. This file therefore
-- records the source-faithful based analogue of Chapter 7's `IsFibration` on `Under (⊤_ TopCat)`.

/-- The based covering homotopy property for a based map `p : E ⟶ B`. -/
class HasBasedCoveringHomotopyProperty {E B : BasedSpace} (p : E ⟶ B) : Prop where
  /-- Every compatible based lift at time `0` of a based homotopy in `B` extends to a based
  lifted homotopy in `E`. -/
  homotopyLift {A : BasedSpace} {f₀ f₁ : A ⟶ B}
      (H : f₀.right.hom HRel[A] f₁.right.hom) (g₀ : A ⟶ E) (hg₀ : g₀ ≫ p = f₀) :
      ∃ g₁ : A ⟶ E,
        ∃ G : g₀.right.hom HRel[A] g₁.right.hom,
          ContinuousMap.comp p.right.hom G.toContinuousMap = H.toContinuousMap

/-- Definition 8.5.1. A based map `p : E ⟶ B` is a based fibration if it is surjective and has
the based covering homotopy property. -/
class IsBasedFibration {E B : BasedSpace} (p : E ⟶ B) : Prop
    extends HasBasedCoveringHomotopyProperty p where
  /-- A based fibration is surjective on underlying points. -/
  surjective : Function.Surjective p.right.hom

namespace HasBasedCoveringHomotopyProperty

variable {E B : BasedSpace} {p : E ⟶ B}

/-- A map with the based covering homotopy property admits lifted based homotopies for every
compatible initial lift. -/
theorem exists_based_homotopyLift [hp : HasBasedCoveringHomotopyProperty p] {A : BasedSpace}
    {f₀ f₁ : A ⟶ B}
    (H : f₀.right.hom HRel[A] f₁.right.hom)
    (g₀ : A ⟶ E) (hg₀ : g₀ ≫ p = f₀) :
    ∃ g₁ : A ⟶ E,
      ∃ G : g₀.right.hom HRel[A] g₁.right.hom,
        ContinuousMap.comp p.right.hom G.toContinuousMap = H.toContinuousMap :=
  hp.homotopyLift H g₀ hg₀

end HasBasedCoveringHomotopyProperty

namespace IsBasedFibration

variable {E B : BasedSpace} {p : E ⟶ B}

/-- An `IsBasedFibration` map is surjective on underlying points. -/
instance instSurjective [hp : IsBasedFibration p] : Function.Surjective p.right.hom :=
  hp.surjective

/-- A based fibration has the based covering homotopy property. -/
theorem exists_based_homotopyLift [hp : IsBasedFibration p] {A : BasedSpace} {f₀ f₁ : A ⟶ B}
    (H : f₀.right.hom HRel[A] f₁.right.hom)
    (g₀ : A ⟶ E) (hg₀ : g₀ ≫ p = f₀) :
    ∃ g₁ : A ⟶ E,
      ∃ G : g₀.right.hom HRel[A] g₁.right.hom,
        ContinuousMap.comp p.right.hom G.toContinuousMap = H.toContinuousMap :=
  HasBasedCoveringHomotopyProperty.exists_based_homotopyLift H g₀ hg₀

end IsBasedFibration
