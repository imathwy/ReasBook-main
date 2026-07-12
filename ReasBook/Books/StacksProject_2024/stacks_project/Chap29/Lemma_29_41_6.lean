import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owners
  `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.UniversallyClosed`, the theorem
  `AlgebraicGeometry.IsProper.toUniversallyClosed`, and the direct instance
  `AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion`.
- Local Chapter 29 precedent records these consequences as source-facing theorem statements from an
  explicit `IsClosedImmersion f` hypothesis, rather than as a recall-only block.
-/

section

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Lemma 29.41.6 (1): a closed immersion is proper. -/
@[stacks 01W5]
theorem closedImmersion_isProper (hf : IsClosedImmersion f) :
    IsProper f := by
  letI : IsClosedImmersion f := hf
  infer_instance

/-- Lemma 29.41.6 (2): a closed immersion is universally closed. -/
@[stacks 01W5]
theorem closedImmersion_universallyClosed (hf : IsClosedImmersion f) :
    UniversallyClosed f := by
  letI : IsClosedImmersion f := hf
  infer_instance

end

end AlgebraicGeometry
