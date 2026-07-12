import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
Chapter 29 already fixes the canonical source-facing owner `Smooth`; mathlib supplies the
open-immersion instance first on `SmoothOfRelativeDimension 0`, and then the canonical bridge
`SmoothOfRelativeDimension.smooth`, so this file remains the thin scheme-level bridge to that
canonical owner without introducing any local wrapper API. -/

/-- Lemma 29.34.6: any open immersion is smooth. -/
@[stacks 01VC]
theorem smooth_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Smooth f := by
  exact (inferInstance : SmoothOfRelativeDimension 0 f).smooth

end AlgebraicGeometry
