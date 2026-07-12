import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

-- Semantic recall: `Flat f` is already available directly from `[Smooth f]` by typeclass
-- inference.

/-- Lemma 29.34.9: a smooth morphism is flat. -/
@[stacks 01VF]
theorem smooth_flat (hf : Smooth f) :
    Flat f := by
  infer_instance

end AlgebraicGeometry
