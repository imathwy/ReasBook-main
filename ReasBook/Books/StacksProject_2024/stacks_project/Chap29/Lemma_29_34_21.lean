import Mathlib
import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap29.Lemma_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the canonical fibre API `Scheme.Hom.fiber` and
  `Scheme.Hom.asFiber`;
- local Chapter 29 precedent represents `dim_x(X_{f(x)})` by `Scheme.Hom.fiberDimensionAt` and
  local scheme dimension by `topologicalKrullDimAt`.
-/

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Lemma 29.34.21: let `f : X ⟶ Y` be a smooth morphism of locally Noetherian schemes. For every
point `x : X`, with image `f x : Y`, the local dimension of `X` at `x` is the local dimension of
`Y` at `f x` plus the local dimension of the fibre `X_{f x}` at `x`. -/
@[stacks 0AFF]
theorem topologicalKrullDimAt_eq_image_add_fiberDimensionAt_of_smooth
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (hf : Smooth f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) + f.fiberDimensionAt x := sorry

end Scheme.Hom
end AlgebraicGeometry
