import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical theorem
  `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`.
- This Stacks item is source-facing: it specializes that canonical flat-mono owner to the
  closed-immersion hypothesis from the source. The source's finite-presentation hypothesis is kept
  on the public theorem surface, while the canonical owner consumed downstream remains
  `LocallyOfFinitePresentation`.
-/

/-- Lemma 29.26.2: a flat closed immersion is an open immersion, hence the inclusion of an open
and closed subscheme of the target. -/
@[stacks 01L3]
theorem isOpenImmersion_of_isClosedImmersion
    (hf : IsClosedImmersion f) [Flat f] [Scheme.Hom.FinitePresentation f] :
    IsOpenImmersion f := sorry

/-- Lemma 29.26.2 companion: the image of a flat closed immersion is clopen in the target. -/
@[stacks 01L3]
theorem isClopen_range_of_flat_closedImmersion
    (hf : IsClosedImmersion f) [Flat f] [Scheme.Hom.FinitePresentation f] :
    IsOpen (Set.range f.base) ∧ IsClosed (Set.range f.base) := sorry

end

end AlgebraicGeometry
