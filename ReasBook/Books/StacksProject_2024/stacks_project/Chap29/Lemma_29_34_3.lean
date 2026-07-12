import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/- Semantic recall / verified owner:
- `lean_leansearch` was rate-limited on this turn;
- direct environment inspection confirmed the canonical scheme-side theorem
  `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`, so the source-facing statement is
  recorded directly on `Smooth f` with the fiber hypothesis expressed via
  `Scheme.Hom.fiberToSpecResidueField`.
-/

/-- Lemma 29.34.3: if a morphism of schemes is flat, locally of finite presentation, and every
fiber over a point of the base is smooth over the corresponding residue field, then the morphism
is smooth. -/
@[stacks 01V8]
theorem smooth_of_flat_of_locallyOfFinitePresentation_of_smoothFibers
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f)
    (hsmooth : ∀ s : S, Smooth (f.fiberToSpecResidueField s)) :
    Smooth f := by
  letI : LocallyOfFinitePresentation f := hfp
  letI : Flat f := hflat
  exact Smooth.of_smooth_fiberToSpecResidueField hsmooth

end AlgebraicGeometry
