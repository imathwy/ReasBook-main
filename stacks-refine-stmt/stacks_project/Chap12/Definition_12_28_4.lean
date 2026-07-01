import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling in the projective/enough-projectives domain:
- mathlib primitive objectwise witness: `ProjectivePresentation X`
- mathlib ambient owner abstraction: `EnoughProjectives C`
- mathlib owner field producing those witnesses: `EnoughProjectives.presentation`
- mathlib owner-derived chosen API under `[EnoughProjectives C]`: `Projective.over X`, `Projective.π X`
- chapter bridge from source-facing left resolutions:
  `CategoryTheory.Abelian.LeftResolution.toEnoughProjectives`

Source/core/bridge triage for Definition 12.28.4:
- source-facing: every object of `C` admits an epimorphism from a projective object.
- core/canonical: `EnoughProjectives C`.
- bridge/view: `EnoughProjectives.presentation` supplies the primitive objectwise witness
  `ProjectivePresentation X`, while `Projective.over X` and `Projective.π X` are the derived
  chosen-object API obtained from the owner abstraction.

Definition 12.28.4 is therefore a `core/canonical` recall item: the textbook notion is already the
mathlib owner class `EnoughProjectives`, so this file should reuse that owner abstraction directly
instead of introducing a parallel wrapper. -/
recall EnoughProjectives

/- Companion recall: the primitive data of `EnoughProjectives C` is
`EnoughProjectives.presentation`, witnessing `Nonempty (ProjectivePresentation X)` for each
`X : C`. -/
recall EnoughProjectives.presentation

/- Companion recall: the primitive objectwise witness for one object is a
`ProjectivePresentation X`. -/
recall ProjectivePresentation

section

variable [EnoughProjectives C]

/- Companion recall: under enough projectives, `Projective.over X` is a chosen projective object
mapping onto `X`. -/
recall Projective.over

/- Companion recall: under enough projectives, `Projective.π X` is the chosen epimorphism
`Projective.over X ⟶ X`. -/
recall Projective.π

end

end

end CategoryTheory
