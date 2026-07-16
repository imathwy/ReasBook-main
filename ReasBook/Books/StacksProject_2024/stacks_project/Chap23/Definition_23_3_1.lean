import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chapters.Chap23.section03

open CategoryTheory
open DividedPowers

universe u

/-
Source/core/bridge triage:
- `source-facing`: a divided power ring, i.e. a triple `(A, I, γ)` of a commutative ring, an ideal,
  and divided powers on that ideal.
- `core/canonical`: the bundled owner `DividedPowerRing` with its category structure from
  `section03`.
- `bridge/view`: the source hom notation `A ⟶ B`, implemented by the canonical
  `DPMorphism A.dividedPowers B.dividedPowers`.
-/

/-
Definition 23.3.1 (Tag 07GU): a divided power ring, written in the source as a triple `(A, I, γ)`
consisting of a commutative ring, an ideal, and divided powers on that ideal, is the canonical
bundled owner `DividedPowerRing`.
-/
recall DividedPowerRing : Type (u + 1)

namespace DividedPowerRing

/-- For divided power rings `A` and `B`, the source morphism type `A ⟶ B` is definitionally the
canonical bundled divided-power morphism type. -/
theorem hom_def (A B : DividedPowerRing) :
    (A ⟶ B) = DPMorphism A.dividedPowers B.dividedPowers :=
  rfl

end DividedPowerRing
