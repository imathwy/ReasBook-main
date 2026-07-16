import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / verified owner check:
- `lean_leansearch` surfaced the canonical owners `topologicalKrullDim`,
  `AlgebraicGeometry.Flat`, and `AlgebraicGeometry.LocallyOfFiniteType`;
- local Chapter 28/29 precedent represents `dim_x(X)` by `topologicalKrullDimAt x` and the source
  hypothesis "relative dimension `d`" by `Scheme.Hom.RelativeDimension f d`, which already includes
  local finite type.
-/

variable {X Y : Scheme.{u}} {d : ℕ}

/-- Lemma 29.29.6: let `f : X ⟶ Y` be a morphism of locally Noetherian schemes which is flat,
locally of finite type, and of relative dimension `d`. For every point `x : X`, with image
`f x : Y`, the local dimension of `X` at `x` is the local dimension of `Y` at `f x` plus `d`. -/
@[stacks 0AFE]
theorem topologicalKrullDimAt_eq_image_add_relativeDimension_of_flat
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [RelativeDimension f d] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) + (d : WithBot ℕ∞) := sorry

end Scheme.Hom
end AlgebraicGeometry
